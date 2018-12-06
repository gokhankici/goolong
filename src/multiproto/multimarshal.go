package multiproto

import (
	"bufio"
	"encoding/binary"
	"fastrpc"
	"io"
	"state"
)

type byteReader interface {
	io.Reader
	ReadByte() (c byte, err error)
}

// Prepare
func (p *Prepare) New() fastrpc.Serializable {
	return &Prepare{0, 0, 0}
}

func (p *Prepare) Marshal(wire io.Writer) {
	var b [9]byte
	bs := b[:9]
	tmp32 := p.t
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = p.inst
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	bs[8] = byte(p.id)
	wire.Write(bs)
}

func (p *Prepare) Unmarshal(wire io.Reader) error {
	var b [9]byte
	bs := b[:9]
	_, err := io.ReadAtLeast(wire, bs, 9)
	p.t = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.inst = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.id = uint8(bs[8])
	return err
}

// Accept
func (p *Accept) New() fastrpc.Serializable {
	return &Accept{0, 0, 0, 0, nil}
}

func (p *Accept) Marshal(wire io.Writer) {
	var b [13]byte
	bs := b[:13]
	tmp32 := p.t
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = p.x
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	tmp32 = p.inst
	bs[8] = byte(tmp32)
	bs[9] = byte(tmp32 >> 8)
	bs[10] = byte(tmp32 >> 16)
	bs[11] = byte(tmp32 >> 24)
	bs[12] = byte(p.id)
	wire.Write(bs)
	bs = b[:]
	alen := int64(len(p.Command))
	if wlen := binary.PutVarint(bs, alen); wlen >= 0 {
		wire.Write(b[0:wlen])
	}
	for i := int64(0); i < alen; i++ {
		p.Command[i].Marshal(wire)
	}
}

func (p *Accept) Unmarshal(rr io.Reader) error {
	var b [13]byte
	bs := b[:13]
	var wire byteReader
	var ok bool
	if wire, ok = rr.(byteReader); !ok {
		wire = bufio.NewReader(rr)
	}
	_, err := io.ReadAtLeast(wire, bs, 13)
	p.t = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.x = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.inst = int32((uint32(bs[8]) | (uint32(bs[9]) << 8) | (uint32(bs[10]) << 16) | (uint32(bs[11]) << 24)))
	p.id = uint8(bs[12])
	alen, err := binary.ReadVarint(wire)
	if err != nil {
		return err
	}
	p.Command = make([]state.Command, alen)
	for i := int64(0); i < alen; i++ {
		p.Command[i].Unmarshal(wire)
	}
	return nil
}

// Reply
func (p *AcceptorReply) New() fastrpc.Serializable {
	return &AcceptorReply{0, 0, 0}
}

func (p *AcceptorReply) Marshal(wire io.Writer) {
	var b [9]byte
	bs := b[:9]
	tmp32 := p.Rw
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = p.Rwt
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	bs[8] = byte(p.Success)
	wire.Write(bs)
}

func (p *AcceptorReply) Unmarshal(wire io.Reader) error {
	var b [9]byte
	bs := b[:9]
	_, err := io.ReadAtLeast(wire, bs, 9)
	p.Rw = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.Rwt = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.Success = uint8(bs[8])
	return err
}

//Commit

func (c *Commit) New() fastrpc.Serializable {
	return &Commit{0, 0}
}

func (c *Commit) Marshal(wire io.Writer) {
	var b [8]byte
	bs := b[:8]
	tmp32 := c.inst
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	tmp32 = c.t
	bs[4] = byte(tmp32)
	bs[5] = byte(tmp32 >> 8)
	bs[6] = byte(tmp32 >> 16)
	bs[7] = byte(tmp32 >> 24)
	wire.Write(bs)
}

func (c *Commit) Unmarshal(wire io.Reader) error {
	var b [8]byte
	bs := b[:8]
	_, err := io.ReadAtLeast(wire, bs, 8)
	c.inst = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	c.t = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	return err
}
