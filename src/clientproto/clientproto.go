package clientproto

import "state"

const (
	PROPOSE uint8 = iota
	PROPOSE_REPLY
)

type Propose struct {
	CommandId int32
	Command   state.Command
}

type ProposeReply struct {
	OK        uint8
	CommandId int32
}
