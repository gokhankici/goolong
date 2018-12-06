package main

import (
	"bufio"
	"clientproto"
	"dlog"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"net"
	"os"
	"state"
	"time"
)

var rounds *int = flag.Int("r", 1, "Split the total number of requests into this many rounds, and do rounds sequentially. Defaults to 1.")
var reqsNb *int = flag.Int("q", 5000, "Total number of requests. Defaults to 5000.")
var writes *int = flag.Int("w", 100, "Percentage of updates (writes). Defaults to 100%.")
var conflicts *int = flag.Int("c", -1, "Percentage of conflicts. Defaults to 0%")
var logfile = flag.String("log", "", "logfile")
var batch = flag.Int("batch", 100, "Commands to send before flush.")

var N int
var successful []int

func main() {
	flag.Parse()
	replicaList := flag.Args()
	N = len(replicaList)
	if *conflicts > 100 {
		log.Fatalf("Conflicts percentage must be between 0 and 100.\n")
	}
	if *logfile != "" {
		f, err := os.OpenFile(*logfile, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0644)
		if err != nil {
			log.Fatal(err)
		}
		defer f.Close()
		log.SetOutput(f)
	}

	put := make([]bool, *reqsNb)
	karray := make([]int64, *reqsNb)

	// building workload
	for i := 0; i < len(karray); i++ {
		r := rand.Intn(100)
		if r < *conflicts {
			karray[i] = 42
		} else {
			karray[i] = int64(43 + i)
		}
		r = rand.Intn(100)
		if r < *writes {
			put[i] = true
		} else {
			put[i] = false
		}
	}
	//connecting to servers
	fmt.Printf("Connecting to replicas..\n")
	servers := make([]net.Conn, N)
	readers := make([]*bufio.Reader, N)
	writers := make([]*bufio.Writer, N)
	for i := 0; i < N; i++ {
		var err error
		servers[i], err = net.Dial("tcp", replicaList[i])
		if err != nil {
			fmt.Printf("Error connecting to replica %d\n", i)
		}
		fmt.Printf("Done connecting to %v\n", i)
		readers[i] = bufio.NewReader(servers[i])
		writers[i] = bufio.NewWriter(servers[i])
	}
	fmt.Printf("Connected to replicas: readers are %v .\n", readers)

	successful = make([]int, N)
	leader := 0
	done := make(chan bool, N)
	var id int32 = 0
	args := clientproto.Propose{CommandId: id, Command: state.Command{Op: state.PUT, K: 0, V: 0}}
	before_total := time.Now()
	// sending requests
	for j := 0; j < *rounds; j++ {

		n := *reqsNb / *rounds
		go waitReplies(readers, leader, n, done)
		before := time.Now()
		for i := 0; i < n; i++ {
			dlog.Printf("Sending proposal %d with put %v, key %v and val %v \n", id, put[i], karray[i], state.Value(i))
			args.CommandId = id
			if put[i] {
				args.Command.Op = state.PUT
			} else {
				args.Command.Op = state.GET
			}
			args.Command.K = state.Key(karray[i])
			args.Command.V = state.Value(i)
			writers[leader].WriteByte(clientproto.PROPOSE)
			args.Marshal(writers[leader])
			if i%*batch == 0 {
				writers[leader].Flush()
			}
			id++
		}
		for i := 0; i < N; i++ {
			writers[i].Flush()
		}
		err := <-done
		after := time.Now()
		fmt.Printf("Round took %v\n", after.Sub(before).Seconds())
		if err {
			dlog.Printf("error: trying new leader.\n")
			leader = (leader + 1) % N
		}
		id++

	}
	after_total := time.Now()
	fmt.Printf("Test took %v\n", after_total.Sub(before_total).Seconds())
	s := 0
	for _, succ := range successful {
		s += succ
	}

	fmt.Printf("Successful: %d\n", s)
}

func waitReplies(readers []*bufio.Reader, leader int, n int, done chan bool) {
	//fmt.Printf("Waiting for %v replies from %v\n", n, leader)
	e := false

	reply := new(clientproto.ProposeReply)
	for i := 0; i < n; i++ {
		dlog.Printf("Waiting for reply from:%v\n", leader)
		if err := reply.Unmarshal(readers[leader]); err != nil {
			dlog.Println("Error when reading:", err)
			e = true
			break
		}
		dlog.Printf("got reply #%v; ok: %v\n", i, reply.OK)
		if reply.OK != 0 {
			successful[leader]++
		}
	}

	done <- e
}
