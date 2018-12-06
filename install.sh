#!/bin/zsh

THIS_DIR=${0:A:h}

build_brisk() {
	make -C $THIS_DIR/Brisk-VCGen/brisk-sequentialize
}

build_briskly() {
	pushd $THIS_DIR/Brisk-VCGen
	stack install
	popd
}

build_benchmarks() {
	make -C $THIS_DIR
}

build_brisk && build_briskly && build_benchmarks
