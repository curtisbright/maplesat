MROOT := $(shell pwd)
export MROOT

maplesat:
	make -C simp rs

clean:
	make -C simp clean
