package paxosproto

import (
	"fastrpc"
	"io"
)

// Prepare
func (p *Prepare) New() fastrpc.Serializable {
	return &Prepare{0, 0}
}

func (p *Prepare) Marshal(wire io.Writer) {
	var b [5]byte
	bs := b[:5]
	tmp32 := p.t
	bs[0] = byte(tmp32)
	bs[1] = byte(tmp32 >> 8)
	bs[2] = byte(tmp32 >> 16)
	bs[3] = byte(tmp32 >> 24)
	bs[4] = byte(p.id)
	wire.Write(bs)
}

func (p *Prepare) Unmarshal(wire io.Reader) error {
	var b [5]byte
	bs := b[:5]
	_, err := io.ReadAtLeast(wire, bs, 5)
	p.t = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.id = uint8(bs[4])
	return err
}

// Accept
func (p *Accept) New() fastrpc.Serializable {
	return &Accept{0, 0, 0}
}

func (p *Accept) Marshal(wire io.Writer) {
	var b [9]byte
	bs := b[:9]
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
	bs[8] = byte(p.id)
	wire.Write(bs)
}

func (p *Accept) Unmarshal(wire io.Reader) error {
	var b [9]byte
	bs := b[:9]
	_, err := io.ReadAtLeast(wire, bs, 9)
	p.t = int32((uint32(bs[0]) | (uint32(bs[1]) << 8) | (uint32(bs[2]) << 16) | (uint32(bs[3]) << 24)))
	p.x = int32((uint32(bs[4]) | (uint32(bs[5]) << 8) | (uint32(bs[6]) << 16) | (uint32(bs[7]) << 24)))
	p.id = uint8(bs[8])
	return err
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
