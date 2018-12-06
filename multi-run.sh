#!/bin/zsh

zparseopts -D -E -- \
	n:=NUMBER_OF_ITER

if [[ $? -ne 0 ]]; then
	echo "argument parsing failed !" >&2
	exit 1
fi

if [[ -z "$NUMBER_OF_ITER" ]]; then
	N=10
else
	N=${NUMBER_OF_ITER[2]}
fi

awkscript='
/^Round took/ {
  val  = $3;
  sum += val;
  n   += 1;
  printf("%-3d %g\n", n, val);
}
END {
  if (n > 0) {
    printf("average: %g\n", sum / n);
  } else {
    printf("awk: input empty\n");
  }
}'

{ for (( i=1; i<=$N; i++ )); do ${0:A:h}/run_paxos.sh $@; done } | \
	awk -F' ' "$awkscript"
