// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package zip

import (
	"bufio"
	"encoding/binary"
	"errors"
	"hash"
	"hash/crc32"
	"io"
	"strings"
)

// TODO(adg): 支持zip文件注释
// TODO(adg): 支持指定deflate压缩级别

// Writer 实现了一个zip文件写入器。
type Writer struct {
	cw            *countWriter
	dir           []*header
	last          *fileWriter
	closed        bool
	globalComment string // 新增全局注释字段
	hiddenComment []byte // 新增隐藏注释字段
}

type header struct {
	*FileHeader
	offset uint64
	raw    bool
}

// NewWriter 返回一个新的Writer，用于向w写入zip文件。
func NewWriter(w io.Writer) *Writer {
	return &Writer{cw: &countWriter{w: bufio.NewWriter(w)}}
}

// SetGlobalComment 设置全局注释
func (w *Writer) SetGlobalComment(comment string) {
	w.globalComment = comment
}

// SetHiddenComment 设置隐藏注释
func (w *Writer) SetHiddenComment(comment []byte) {
	w.hiddenComment = comment
}

// SetOffset 设置zip数据在底层写入器中的起始偏移量。
// 当zip数据附加到现有文件（如二进制可执行文件）时应使用此方法。
// 必须在写入任何数据之前调用。
func (w *Writer) SetOffset(n int64) {
	if w.cw.count != 0 {
		panic("zip: SetOffset called after data was written")
	}
	w.cw.count = n
}

// Flush 将任何缓冲数据刷新到底层写入器。
// 通常不需要调用Flush；调用Close就足够了。
func (w *Writer) Flush() error {
	return w.cw.w.(*bufio.Writer).Flush()
}

// Close 通过写入中央目录完成zip文件的写入。
// 它不会（也不能）关闭底层写入器。
func (w *Writer) Close() error {
	if w.last != nil && !w.last.closed {
		if err := w.last.close(); err != nil {
			return err
		}
		w.last = nil
	}
	if w.closed {
		return errors.New("zip: writer closed twice")
	}
	w.closed = true

	// 写入中央目录
	start := w.cw.count
	for _, h := range w.dir {
		var buf [directoryHeaderLen]byte
		b := writeBuf(buf[:])
		b.uint32(uint32(directoryHeaderSignature))
		b.uint16(h.CreatorVersion)
		b.uint16(h.ReaderVersion)
		b.uint16(h.Flags)
		b.uint16(h.Method)
		b.uint16(h.ModifiedTime)
		b.uint16(h.ModifiedDate)
		b.uint32(h.CRC32)
		if h.isZip64() || h.offset > uint32max {
			// 该文件需要zip64头。在两个32位大小字段中存储maxint
			// （稍后还有偏移量）来表示应使用zip64额外头。
			b.uint32(uint32max) // 压缩大小
			b.uint32(uint32max) // 未压缩大小

			// 向Extra追加zip64额外块
			var buf [28]byte // 2x uint16 + 3x uint64
			eb := writeBuf(buf[:])
			eb.uint16(zip64ExtraId)
			eb.uint16(24) // size = 3x uint64
			eb.uint64(h.UncompressedSize64)
			eb.uint64(h.CompressedSize64)
			eb.uint64(h.offset)
			h.Extra = append(h.Extra, buf[:]...)
		} else {
			b.uint32(h.CompressedSize)
			b.uint32(h.UncompressedSize)
		}
		b.uint16(uint16(len(h.Name)))
		b.uint16(uint16(len(h.Extra)))
		b.uint16(uint16(len(h.Comment)))
		b = b[4:] // 跳过磁盘号起始和内部文件属性（2x uint16）
		b.uint32(h.ExternalAttrs)
		if h.offset > uint32max {
			b.uint32(uint32max)
		} else {
			b.uint32(uint32(h.offset))
		}
		if _, err := w.cw.Write(buf[:]); err != nil {
			return err
		}
		if _, err := io.WriteString(w.cw, h.Name); err != nil {
			return err
		}
		if _, err := w.cw.Write(h.Extra); err != nil {
			return err
		}
		if _, err := io.WriteString(w.cw, h.Comment); err != nil {
			return err
		}
	}
	end := w.cw.count

	records := uint64(len(w.dir))
	size := uint64(end - start)
	offset := uint64(start)

	if records > uint16max || size > uint32max || offset > uint32max {
		var buf [directory64EndLen + directory64LocLen]byte
		b := writeBuf(buf[:])

		// zip64中央目录结束记录
		b.uint32(directory64EndSignature)
		b.uint64(directory64EndLen - 12) // 长度减去签名（uint32）和长度字段（uint64）
		b.uint16(zipVersion45)           // 创建版本
		b.uint16(zipVersion45)           // 提取所需版本
		b.uint32(0)                      // 此磁盘号
		b.uint32(0)                      // 包含中央目录起始的磁盘号
		b.uint64(records)                // 此磁盘上中央目录中的条目总数
		b.uint64(records)                // 中央目录中的条目总数
		b.uint64(size)                   // 中央目录大小
		b.uint64(offset)                 // 中央目录起始相对于起始磁盘号的偏移量

		// zip64中央目录结束定位器
		b.uint32(directory64LocSignature)
		b.uint32(0)           // 包含zip64中央目录结束记录的磁盘号
		b.uint64(uint64(end)) // zip64中央目录结束记录的相对偏移量
		b.uint32(1)           // 磁盘总数

		if _, err := w.cw.Write(buf[:]); err != nil {
			return err
		}

		// 在常规结束记录中存储最大值，以表示应使用zip64值
		records = uint16max
		size = uint32max
		offset = uint32max
	}

	// 写入结束记录
	var buf [directoryEndLen]byte
	b := writeBuf(buf[:])
	b.uint32(uint32(directoryEndSignature))
	b = b[4:]                 // 跳过磁盘号和第一个磁盘号（2x uint16）
	b.uint16(uint16(records)) // 此磁盘上的条目数
	b.uint16(uint16(records)) // 总条目数
	b.uint32(uint32(size))    // 目录大小
	b.uint32(uint32(offset))  // 目录起始位置
	// 计算并设置注释长度
	commentBytes := []byte(w.globalComment)
	commentLength := uint16(len(commentBytes))
	// 写入注释长度
	if commentLength > 0 {
		b.uint16(commentLength) // 注释长度
	}

	if _, err := w.cw.Write(buf[:]); err != nil {
		return err
	}
	// 写入全局注释
	if commentLength > 0 {
		if _, err := w.cw.Write(commentBytes); err != nil {
			return err
		}
	}
	// 写入 hiddenMetadataSignature
	if w.hiddenComment != nil && len(w.hiddenComment) > 0 {
		var sigBuf [8]byte
		sigWriteBuf := writeBuf(sigBuf[:])
		sigWriteBuf.uint64(uint64(hiddenMetadataSignature)) // 写入 hiddenMetadataSignature
		if _, err := w.cw.Write(sigBuf[:]); err != nil {
			return err
		}
	}

	// 写入隐藏注释
	if w.hiddenComment != nil && len(w.hiddenComment) > 0 {
		if _, err := w.cw.Write(w.hiddenComment); err != nil {
			return err
		}
	}

	return w.cw.w.(*bufio.Writer).Flush()
}

func (w *Writer) IsClosed() bool {
	return w.closed
}

// Create 使用提供的名称向zip文件添加一个文件。
// 它返回一个Writer，文件内容应写入其中。
// 名称必须是相对路径：不能以驱动器字母（例如C:）或前导斜杠开头，
// 并且只允许使用正斜杠。
// 在下一次调用Create、CreateHeader或Close之前，必须将文件内容写入io.Writer。
func (w *Writer) Create(name string) (io.Writer, error) {
	header := &FileHeader{
		Name:   name,
		Method: Deflate,
	}
	return w.CreateHeader(header)
}

// CreateHeader 使用提供的FileHeader为文件元数据向zip文件添加一个文件。
// 它返回一个Writer，文件内容应写入其中。
//
// 在下一次调用Create、CreateHeader或Close之前，必须将文件内容写入io.Writer。
// 提供的FileHeader fh在调用CreateHeader后不得修改。
func (w *Writer) CreateHeader(fh *FileHeader) (io.Writer, error) {
	if err := w.prepare(fh); err != nil {
		return nil, err
	}

	fh.Flags |= 0x8 // 我们将写入数据描述符
	// TODO(alex): 查看规范，看看在使用加密时是否需要更改这些值。
	// when using encryption.
	fh.CreatorVersion = fh.CreatorVersion&0xff00 | zipVersion20 // 保留兼容性字节
	fh.ReaderVersion = zipVersion20

	fw := &fileWriter{
		zipw:      w.cw,
		compCount: &countWriter{w: w.cw},
		crc32:     crc32.NewIEEE(),
	}
	// 在可能由于密码而将Method更改为99之前获取压缩器
	comp := compressor(fh.Method)
	if comp == nil {
		return nil, ErrAlgorithm
	}
	// 检查密码
	var sw io.Writer = fw.compCount
	if fh.password != nil {
		if fh.encryption == StandardEncryption {
			ew, err := ZipCryptoEncryptor(sw, fh.password, fw)
			if err != nil {
				return nil, err
			}
			sw = ew
		} else {
			// 我们有密码需要加密。
			fh.writeWinZipExtra()
			fh.Method = WinZipAes // 可以更改，因为我们已经获取了压缩器并写入了额外信息
			ew, err := newEncryptionWriter(sw, fh.password, fw, fh.aesStrength)
			if err != nil {
				return nil, err
			}
			sw = ew
		}
	}
	var err error
	fw.comp, err = comp(sw)
	if err != nil {
		return nil, err
	}
	fw.rawCount = &countWriter{w: fw.comp}

	h := &header{
		FileHeader: fh,
		offset:     uint64(w.cw.count),
	}
	w.dir = append(w.dir, h)
	fw.header = h

	if err := writeHeader(w.cw, h); err != nil {
		return nil, err
	}

	w.last = fw
	return fw, nil
}

func writeHeader(w io.Writer, h *header) error {
	var buf [fileHeaderLen]byte
	b := writeBuf(buf[:])
	b.uint32(uint32(fileHeaderSignature))
	b.uint16(h.ReaderVersion)
	b.uint16(h.Flags)
	b.uint16(h.Method)
	b.uint16(h.ModifiedTime)
	b.uint16(h.ModifiedDate)
	// In raw mode (caller does the compression), the values are either
	// written here or in the trailing data descriptor based on the header
	// flags.
	if h.raw && !h.hasDataDescriptor() {
		b.uint32(h.CRC32)
		b.uint32(uint32(min(h.CompressedSize64, uint32max)))
		b.uint32(uint32(min(h.UncompressedSize64, uint32max)))
	} else {
		// When this package handle the compression, these values are
		// always written to the trailing data descriptor.
		b.uint32(0) // crc32
		b.uint32(0) // compressed size
		b.uint32(0) // uncompressed size
	}
	b.uint16(uint16(len(h.Name)))
	b.uint16(uint16(len(h.Extra)))
	if _, err := w.Write(buf[:]); err != nil {
		return err
	}
	if _, err := io.WriteString(w, h.Name); err != nil {
		return err
	}
	_, err := w.Write(h.Extra)
	return err
}

type fileWriter struct {
	*header
	zipw      io.Writer
	rawCount  *countWriter
	comp      io.WriteCloser
	compCount *countWriter
	crc32     hash.Hash32
	closed    bool

	hmac hash.Hash // possible hmac used for authentication when encrypting
}

func (w *fileWriter) Write(p []byte) (int, error) {
	if w.closed {
		return 0, errors.New("zip: write to closed file")
	}
	if w.raw {
		return w.zipw.Write(p)
	}
	w.crc32.Write(p)
	return w.rawCount.Write(p)
}

func (w *fileWriter) close() error {
	if w.closed {
		return errors.New("zip: file closed twice")
	}
	w.closed = true
	if w.raw {
		return w.writeDataDescriptor()
	}
	if err := w.comp.Close(); err != nil {
		return err
	}
	// if encrypted grab the hmac and write it out
	if w.header.IsEncrypted() && w.header.encryption != StandardEncryption {
		authCode := w.hmac.Sum(nil)
		authCode = authCode[:10]
		_, err := w.compCount.Write(authCode)
		if err != nil {
			return errors.New("zip: error writing authcode")
		}
	}
	// update FileHeader
	fh := w.header.FileHeader
	// ae-2 we don't write out CRC
	if !fh.IsEncrypted() || fh.encryption == StandardEncryption {
		fh.CRC32 = w.crc32.Sum32()
	}
	fh.CompressedSize64 = uint64(w.compCount.count)
	fh.UncompressedSize64 = uint64(w.rawCount.count)

	if fh.isZip64() {
		fh.CompressedSize = uint32max
		fh.UncompressedSize = uint32max
		fh.ReaderVersion = zipVersion45 // requires 4.5 - File uses ZIP64 format extensions
	} else {
		fh.CompressedSize = uint32(fh.CompressedSize64)
		fh.UncompressedSize = uint32(fh.UncompressedSize64)
	}

	// Write data descriptor. This is more complicated than one would
	// think, see e.g. comments in zipfile.c:putextended() and
	// http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=7073588.
	// The approach here is to write 8 byte sizes if needed without
	// adding a zip64 extra in the local header (too late anyway).
	var buf []byte
	if fh.isZip64() {
		buf = make([]byte, dataDescriptor64Len)
	} else {
		buf = make([]byte, dataDescriptorLen)
	}
	b := writeBuf(buf)
	b.uint32(dataDescriptorSignature) // de-facto standard, required by OS X
	b.uint32(fh.CRC32)
	if fh.isZip64() {
		b.uint64(fh.CompressedSize64)
		b.uint64(fh.UncompressedSize64)
	} else {
		b.uint32(fh.CompressedSize)
		b.uint32(fh.UncompressedSize)
	}
	_, err := w.zipw.Write(buf)
	return err
}

func (w *fileWriter) writeDataDescriptor() error {
	if !w.hasDataDescriptor() {
		return nil
	}
	// Write data descriptor. This is more complicated than one would
	// think, see e.g. comments in zipfile.c:putextended() and
	// https://bugs.openjdk.org/browse/JDK-7073588.
	// The approach here is to write 8 byte sizes if needed without
	// adding a zip64 extra in the local header (too late anyway).
	var buf []byte
	if w.isZip64() {
		buf = make([]byte, dataDescriptor64Len)
	} else {
		buf = make([]byte, dataDescriptorLen)
	}
	b := writeBuf(buf)
	b.uint32(dataDescriptorSignature) // de-facto standard, required by OS X
	b.uint32(w.CRC32)
	if w.isZip64() {
		b.uint64(w.CompressedSize64)
		b.uint64(w.UncompressedSize64)
	} else {
		b.uint32(w.CompressedSize)
		b.uint32(w.UncompressedSize)
	}
	_, err := w.zipw.Write(buf)
	return err
}

type countWriter struct {
	w     io.Writer
	count int64
}

func (w *countWriter) Write(p []byte) (int, error) {
	n, err := w.w.Write(p)
	w.count += int64(n)
	return n, err
}

type nopCloser struct {
	io.Writer
}

func (w nopCloser) Close() error {
	return nil
}

type writeBuf []byte

func (b *writeBuf) uint8(v uint8) {
	(*b)[0] = v
	*b = (*b)[1:]
}

func (b *writeBuf) uint16(v uint16) {
	binary.LittleEndian.PutUint16(*b, v)
	*b = (*b)[2:]
}

func (b *writeBuf) uint32(v uint32) {
	binary.LittleEndian.PutUint32(*b, v)
	*b = (*b)[4:]
}

func (b *writeBuf) uint64(v uint64) {
	binary.LittleEndian.PutUint64(*b, v)
	*b = (*b)[8:]
}

//////////////////

// prepare performs the bookkeeping operations required at the start of
// CreateHeader and CreateRaw.
func (w *Writer) prepare(fh *FileHeader) error {
	if w.last != nil && !w.last.closed {
		if err := w.last.close(); err != nil {
			return err
		}
	}
	if len(w.dir) > 0 && w.dir[len(w.dir)-1].FileHeader == fh {
		// See https://golang.org/issue/11144 confusion.
		return errors.New("archive/zip: invalid duplicate FileHeader")
	}
	return nil
}

type dirWriter struct{}

func (dirWriter) Write(b []byte) (int, error) {
	if len(b) == 0 {
		return 0, nil
	}
	return 0, errors.New("zip: write to directory")
}

// CreateRaw adds a file to the zip archive using the provided [FileHeader] and
// returns a [Writer] to which the file contents should be written. The file's
// contents must be written to the io.Writer before the next call to [Writer.Create],
// [Writer.CreateHeader], [Writer.CreateRaw], or [Writer.Close].
//
// In contrast to [Writer.CreateHeader], the bytes passed to Writer are not compressed.
//
// CreateRaw's argument is stored in w. If the argument is a pointer to the embedded
// [FileHeader] in a [File] obtained from a [Reader] created from in-memory data,
// then w will refer to all of that memory.
func (w *Writer) CreateRaw(fh *FileHeader) (io.Writer, error) {
	if err := w.prepare(fh); err != nil {
		return nil, err
	}

	fh.CompressedSize = uint32(min(fh.CompressedSize64, uint32max))
	fh.UncompressedSize = uint32(min(fh.UncompressedSize64, uint32max))

	h := &header{
		FileHeader: fh,
		offset:     uint64(w.cw.count),
		raw:        true,
	}
	w.dir = append(w.dir, h)
	if err := writeHeader(w.cw, h); err != nil {
		return nil, err
	}

	if strings.HasSuffix(fh.Name, "/") {
		w.last = nil
		return dirWriter{}, nil
	}

	fw := &fileWriter{
		header: h,
		zipw:   w.cw,
	}
	w.last = fw
	return fw, nil
}

// Copy copies the file f (obtained from a [Reader]) into w. It copies the raw
// form directly bypassing decompression, compression, and validation.
func (w *Writer) Copy(f *File) error {
	r, err := f.OpenRaw()
	if err != nil {
		return err
	}
	// Copy the FileHeader so w doesn't store a pointer to the data
	// of f's entire archive. See #65499.
	fh := f.FileHeader
	if f.IsEncrypted() && f.encryption != StandardEncryption {
		fh.Method = WinZipAes
	}

	fw, err := w.CreateRaw(&fh)
	if err != nil {
		return err
	}
	_, err = io.Copy(fw, r)
	return err
}
