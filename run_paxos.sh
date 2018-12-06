#!/bin/zsh

zparseopts -D -E -- \
	b=BATCH \
	c:=CONFLICT_PERC q:=REQUEST_COUNT r:=ROUND_COUNT w:=WRITE_PERC \
	h=HELP -help=HELP

if [[ -n "$HELP" ]]; then
	cat <<EOF
usage: 
  -b : batch
  -c : conflict percentage
  -q : request count
  -r : round count
  -w : write percentage
EOF
	exit 0
fi

blue()  { print -P "%F{blue}%B$1%b%f" }
green() { print -P "%F{green}%B$1%b%f" }
red()   { print -P "%F{red}%B$1%b%f" }

# trap CTRL-C input, and kill every process created
trap "pkill -P $$; sleep 1; exit 1;" INT


ADDR="127.0.0.1"
ADDRS=( "$ADDR:7070" "$ADDR:7071" "$ADDR:7072" )
LOG_FILES=( "log0" "log1" "log2" )

blue "running multi paxos with ${#ADDRS} servers and a client ..."

make -C ${0:A:h}

for ((i = 1; i <= ${#ADDRS}; i++)); do
	bin/multipaxos $BATCH -addr "$ADDRS[$i]" -id $((i - 1)) -log "log$i" ${ADDRS[@]} &
done

sleep 3

bin/client -log 'logc' \
	$CONFLICT_PERC $REQUEST_COUNT $ROUND_COUNT $WRITE_PERC \
	${ADDRS[@]}

pkill -P $$
sleep 1

green "DONE !"
