package multiproto

import (
	"bufio"
	"clientproto"
	"dlog"
	"fastrpc"
	"fmt"
	"gochai"
	"io"
	"log"
	"net"
	"state"
)

const CHAN_BUFFER_SIZE = 200000

const (
	PrepareType uint8 = 0
	AcceptType        = 1
)

type Propose struct {
	*clientproto.Propose
	Wire *bufio.Writer
}

type Prepare struct {
	id   uint8
	t    int32
	inst int32
}

type AcceptorReply struct {
	Success uint8
	Rwt     int32
	Rw      int32
}

type Accept struct {
	id      uint8
	t       int32
	x       int32
	inst    int32
	Command []state.Command
}

type Commit struct {
	inst int32
	t    int32
}

type Batch struct {
	Id       int32
	Commands []state.Command
	Props    []*Propose
}

type MultiNode struct {
	*gochai.ChaiNode // extends ChaiNode
	prepareRPC       uint8
	prepareChans     []chan fastrpc.Serializable
	acceptRPC        uint8
	acceptChans      []chan fastrpc.Serializable
	replyRPC         uint8
	replyChans       []chan fastrpc.Serializable
	CommitRPC        uint8
	CommitChans      []chan fastrpc.Serializable
	ProposeChan      chan *Propose // channel for client proposals
	State            *state.State
	CrtInstance      int32
	CommittedUpTo    int32
}

func NewMultiNode(name string, id int, myaddr string, peerAddrList []string, isServer bool) *MultiNode {
	n := &MultiNode{
		gochai.CreateNewNode(name, id, myaddr, peerAddrList, isServer),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		0,
		make([]chan fastrpc.Serializable, len(peerAddrList)),
		make(chan *Propose, CHAN_BUFFER_SIZE),
		state.InitState(),
		0, -1}

	n.prepareRPC = n.RegisterRPC(new(Prepare), n.prepareChans)
	n.acceptRPC = n.RegisterRPC(new(Accept), n.acceptChans)
	n.replyRPC = n.RegisterRPC(new(AcceptorReply), n.replyChans)
	n.CommitRPC = n.RegisterRPC(new(Commit), n.CommitChans)
	for i := range n.prepareChans {
		n.prepareChans[i] = make(chan fastrpc.Serializable, CHAN_BUFFER_SIZE)
		n.acceptChans[i] = make(chan fastrpc.Serializable, CHAN_BUFFER_SIZE)
		n.replyChans[i] = make(chan fastrpc.Serializable, CHAN_BUFFER_SIZE)
		n.CommitChans[i] = make(chan fastrpc.Serializable, CHAN_BUFFER_SIZE)
	}
	return n
}

func (n *MultiNode) Run() {
	fmt.Printf("Starting.\n")
	n.Start()
	fmt.Printf("Done starting.\n")
	if !n.IsServer {
		go n.WaitForClientConnections()
	}
}

func (n *MultiNode) MakeUniqueBallot(ballot int32) int32 {
	return (ballot << 4) | n.MyId()
}

// =================
//  Peer connections
// =================

// Sending and Receiving
func (n *MultiNode) SendPrepare(id int, repId *gochai.UInt8, term *gochai.IntVar, inst *gochai.IntVar) {
	msg := &Prepare{id: repId.Get(), t: term.Get(), inst: inst.Get()}
	n.NSend(id, n.prepareRPC, msg)
}

func (n *MultiNode) SendAccept(id int, repId *gochai.UInt8, term *gochai.IntVar, val *gochai.IntVar, inst *gochai.IntVar, batch *Batch) {
	msg := &Accept{id: repId.Get(), t: term.Get(), x: val.Get(), inst: inst.Get(), Command: batch.Commands}
	n.NSend(id, n.acceptRPC, msg)
}

func (n *MultiNode) AcceptorReceive() (msgType *gochai.UInt8, id *gochai.UInt8, instance *gochai.IntVar, term *gochai.IntVar, value *gochai.IntVar, commands []state.Command) {
	allChans := n.prepareChans
	allChans = append(allChans, n.acceptChans...)
	msg := n.RecvAll(allChans)
	switch msg.(type) {
	case *Prepare:
		prep := msg.(*Prepare)
		return gochai.NewUInt8_(PrepareType), gochai.NewUInt8_(prep.id), gochai.NewIntVar_(prep.inst), gochai.NewIntVar_(prep.t), gochai.NewIntVar_(-1), nil
	case *Accept:
		acc := msg.(*Accept)
		return gochai.NewUInt8_(AcceptType), gochai.NewUInt8_(acc.id), gochai.NewIntVar_(acc.inst), gochai.NewIntVar_(acc.t), gochai.NewIntVar_(acc.x), acc.Command
	}
	return nil, nil, nil, nil, nil, nil
}

func (n *MultiNode) SendAcceptorReply(id int, rwt int32, rw int32, success uint8) {
	msg := &AcceptorReply{Rwt: rwt, Rw: rw, Success: success}
	n.NSend(id, n.replyRPC, msg)
}

func (n *MultiNode) RecvAcceptorReplyFrom(id int) (*gochai.IntVar, *gochai.IntVar, *gochai.UInt8) {
	msg := n.RecvFromGen(id, n.replyChans).(*AcceptorReply)
	return gochai.NewIntVar_(msg.Rwt), gochai.NewIntVar_(msg.Rw), gochai.NewUInt8_(msg.Success)
}

func (n *MultiNode) BroadcastCommit(t int32, inst int32) {
	for id := range n.PeerIds {
		dlog.Printf("sending commit of instance %v and ballot %v to %v", inst, t, id)
		n.SendCommit(id, t, inst)
	}
	dlog.Printf("done\n")
}

func (n *MultiNode) SendCommit(id int, t int32, inst int32) {
	msg := &Commit{t: t, inst: inst}
	n.NSend(id, n.CommitRPC, msg)
}

func (n *MultiNode) RecvCommit() (int32, int32) {
	msg := n.RecvAll(n.CommitChans).(*Commit)
	return msg.inst, msg.t
}

// ====================
//  Client connections
// ====================

/* Client connections dispatcher */
func (n *MultiNode) WaitForClientConnections() {
	fmt.Printf("Waiting for connections...\n")
	for !n.Stop {
		conn, err := n.Listener.Accept()
		if err != nil {
			log.Println("Accept error:", err)
			continue
		}
		fmt.Printf("Accepted connection from: %v\n", conn.RemoteAddr())
		go n.clientListener(conn)
	}
}

func (n *MultiNode) clientListener(conn net.Conn) {
	reader := bufio.NewReader(conn)
	writer := bufio.NewWriter(conn)
	var msgType byte
	var err error
	for !n.Stop && err == nil {

		if msgType, err = reader.ReadByte(); err != nil {
			break
		}
		switch uint8(msgType) {

		case clientproto.PROPOSE:
			prop := new(clientproto.Propose)
			if err = prop.Unmarshal(reader); err != nil {
				break
			}
			n.ProposeChan <- &Propose{prop, writer}
			break

		}
	}
	if err != nil && err != io.EOF {
		dlog.Println("Error when reading from client connection:", err)
	}
}

func (n *MultiNode) ReplyPropose(ok uint8, batch *Batch) {
	for _, prop := range batch.Props {
		reply := &clientproto.ProposeReply{OK: ok, CommandId: prop.CommandId}
		wire := prop.Wire
		reply.Marshal(wire)
		wire.Flush()
		dlog.Printf("Sent reply %v for proposal with id %v\n.", ok, prop.CommandId)
	}
}
