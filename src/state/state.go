package state

type Operation uint8

const (
	NONE Operation = iota
	PUT
	GET
)

type Value int32

const NIL Value = 0

type Key int32

type Command struct {
	Op Operation
	K  Key
	V  Value
}

type State struct {
	Store map[Key]Value
}

func InitState() *State {
	return &State{make(map[Key]Value)}
}

func (c *Command) Execute(st *State) Value {

	switch c.Op {
	case PUT:
		st.Store[c.K] = c.V
		return c.V

	case GET:
		if val, present := st.Store[c.K]; present {
			return val
		}
	}
	return NIL
}
