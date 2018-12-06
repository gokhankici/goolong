package paxosproto

import (
	"fastrpc"
	"gochai"
	"state"
)

const (
	PrepareType uint8 = 0
	AcceptType        = 1
)

type Prepare struct {
	id uint8
	t  int32
}

type AcceptorReply struct {
	Success uint8
	Rwt     int32
	Rw      int32
}

type Accept struct {
	id uint8
	t  int32
	x  int32
}

type Commit struct {
	inst    int32
	t       int32
	Command []state.Command
}

type PaxosNode struct {
	*gochai.ChaiNode // extends ChaiNode
	prepareRPC       uint8
	prepareChans     []chan fastrpc.Serializable
	acceptRPC        uint8
	acceptChans      []chan fastrpc.Serializable
	replyRPC         uint8
	replyChans       []chan fastrpc.Serializable
}

func NewPaxosNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *PaxosNode {
	n := &PaxosNode{
		gochai.CreateNewNode(name, id, myaddr, peerAddrList, isServer),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList))}

	n.prepareRPC = n.RegisterRPC(new(Prepare), n.prepareChans)
	n.acceptRPC = n.RegisterRPC(new(Accept), n.acceptChans)
	n.replyRPC = n.RegisterRPC(new(AcceptorReply), n.replyChans)
	for i := range n.prepareChans {
		n.prepareChans[i] = make(chan fastrpc.Serializable)
		n.acceptChans[i] = make(chan fastrpc.Serializable)
		n.replyChans[i] = make(chan fastrpc.Serializable)
	}
	return n
}

// Sending and Receiving
func (n *PaxosNode) SendPrepare(id int, repId *gochai.UInt8, term *gochai.IntVar) {
	msg := &Prepare{id: repId.Get(), t: term.Get()}
	n.NSend(id, n.prepareRPC, msg)
}

func (n *PaxosNode) SendAccept(id int, repId *gochai.UInt8, term *gochai.IntVar, val *gochai.IntVar) {
	msg := &Accept{id: repId.Get(), t: term.Get(), x: val.Get()}
	n.NSend(id, n.acceptRPC, msg)
}

func (n *PaxosNode) AcceptorReceive() (msgType *gochai.UInt8, id *gochai.UInt8, term *gochai.IntVar, value *gochai.IntVar) {
	allChans := n.prepareChans
	allChans = append(allChans, n.acceptChans...)
	msg := n.RecvAll(allChans)
	switch msg.(type) {
	case *Prepare:
		prep := msg.(*Prepare)

		return gochai.NewUInt8_(PrepareType), gochai.NewUInt8_(prep.id), gochai.NewIntVar_(prep.t), gochai.NewIntVar_(-1)
	case *Accept:
		acc := msg.(*Accept)
		return gochai.NewUInt8_(AcceptType), gochai.NewUInt8_(acc.id), gochai.NewIntVar_(acc.t), gochai.NewIntVar_(acc.x)
	}
	return nil, nil, nil, nil
}

func (n *PaxosNode) SendAcceptorReply(id int, rwt *gochai.IntVar, rw *gochai.IntVar, success *gochai.UInt8) {
	msg := &AcceptorReply{Rwt: rwt.Get(), Rw: rw.Get(), Success: success.Get()}
	n.NSend(id, n.replyRPC, msg)
}

func (n *PaxosNode) RecvAcceptorReplyFrom(id int) (*gochai.IntVar, *gochai.IntVar, *gochai.UInt8) {
	msg := n.RecvFromGen(id, n.replyChans).(*AcceptorReply)
	return gochai.NewIntVar_(msg.Rwt), gochai.NewIntVar_(msg.Rw), gochai.NewUInt8_(msg.Success)
}
