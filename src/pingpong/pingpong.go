package main

import (
	"flag"
	"fmt"
	"gochai"
)

var server = flag.Bool("server", true, "Act as server (true) or client (false). ")

// HACK: we should ensure that these are defined and match the names in Creatnewnode.
const m = 0
const c = 1

func main() {
	flag.Parse()
	if *server {
		runServerProtocol()
	} else {
		runClientProtocol()
	}
}

func runClientProtocol() {
	n := gochai.CreateNewNode("c", c, ":7071", []string{":7070"}, false)
	lc := gochai.NewVar()
	lc.Assign(42)
	rc := gochai.NewVar()
	rc.Assign(1)
	fmt.Printf("Acting as client %v. Sending  pair %v, %v \n", n.MyId(), lc.Get(), rc.Get())
	n.SendPair(m, lc, rc)
	n.Shutdown()
}

func runServerProtocol() {
	fmt.Println("Acting as server.")
	n := gochai.CreateNewNode("m", m, ":7070", []string{":7071"}, true)
	l, r := n.RecvPair()
	fmt.Printf("Received pair: %v, %v", l.Get(), r.Get())
	n.Shutdown()
}

// {-@ ensures: and([l=42,r=1])	-@}
