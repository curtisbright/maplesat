MROOT := $(shell pwd)
export MROOT

all: maplesat_static_3 maplesat_static_9 maplesat_static_15 maplesat_static_21 maplesat_static_27 maplesat_static_33 maplesat_static_39 maplesat_static_45 maplesat_static_51 maplesat_static_57 maplesat_static_63 maplesat_static_69

maplesat_static_%:
	echo "#define N $*" > core/defineN.h
	rm -f core/Solver.or
	make -C simp rs
	mv simp/maplesat_static simp/maplesat_static_AD_$*

debug:
	make -C simp d

clean:
	make -C simp clean
