%: %.scm
	cp $^ in.scm
	csi -e '(load "bit.scm") (byte-compile "in.scm" "out.c")'
	gcc out.c bit.c -o $@
	rm in.scm out.c
