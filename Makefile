%.c: %.scm
	cat $^ | csi -e '(load "bit.scm") (byte-compile)' > $*.c

%: %.c
	gcc $^ bit.c -o $@

%-ex.scm: %.scm
	cat alexpander.scm $^ > $@
