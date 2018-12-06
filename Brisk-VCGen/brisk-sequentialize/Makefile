all: brisk
brisk: brisk.sav
	spld --output="brisk" --main=restore --moveable --static --resources-from-sav --resources=brisk.sav=/brisk/bri.sav

brisk.sav: rewrite.pl
	sicstus --goal "compile('run_brisk.pl'), save_program('brisk.sav'), halt."
clean :
	rm brisk brisk.sav
