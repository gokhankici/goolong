THIS_DIR   = $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
GO         = env GOPATH="$(THIS_DIR)" go
GO_BUILD   = $(GO) build
GO_INSTALL = $(GO) install
BIN_DIR    = $(THIS_DIR)/bin

NAMES    = twopc paxos multipaxos client paxoschk multipaxoschk
BINARIES = $(patsubst %,bin/%,$(NAMES))

.PHONY: clean

all: $(BINARIES)

.SECONDEXPANSION: 
bin/%: MODULENAME = $(notdir $@)
bin/%: BINPREQ    = src/$(MODULENAME)/$(MODULENAME).go

$(BINARIES): bin/%: $$(BINPREQ)
	$(GO_BUILD) $*
	$(GO_INSTALL) $*

clean:
	$(GO) clean -i $(patsubst bin/%,%,$(BINARIES))
	rm -f $(NAMES)
