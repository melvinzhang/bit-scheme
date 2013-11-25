SHELL=/bin/bash

%.c: %.scm
	cat $^ | csi -e '(load "bit.scm") (byte-compile)' > $*.c

%: %.c
	gcc $^ bit.c -o $@

%-ex.scm: %.scm
	cat alexpander.scm $^ > $@

test-reader: reader
	for i in *.scm; do echo $$i; diff <(cat $$i | ./reader) <(cat $$i | csi -q read-all.scm); done
