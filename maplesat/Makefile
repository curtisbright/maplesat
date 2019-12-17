MROOT := $(shell pwd)
export MROOT

all: maplesat_static_1a maplesat_static_1b maplesat_static_1c maplesat_static_2 maplesat_static_3 maplesat_static_4 maplesat_static_5 maplesat_static_6a maplesat_static_6b maplesat_static_6c

maplesat_static_1a:
	touch core/Solver.cc
	make -C simp maplesat_static_1a

maplesat_static_1b:
	touch core/Solver.cc
	make -C simp maplesat_static_1b

maplesat_static_1c:
	touch core/Solver.cc
	make -C simp maplesat_static_1c

maplesat_static_2:
	touch core/Solver.cc
	make -C simp maplesat_static_2

maplesat_static_3:
	touch core/Solver.cc
	make -C simp maplesat_static_3

maplesat_static_4:
	touch core/Solver.cc
	make -C simp maplesat_static_4

maplesat_static_5:
	touch core/Solver.cc
	make -C simp maplesat_static_5

maplesat_static_6a:
	touch core/Solver.cc
	make -C simp maplesat_static_6a

maplesat_static_6b:
	touch core/Solver.cc
	make -C simp maplesat_static_6b

maplesat_static_6c:
	touch core/Solver.cc
	make -C simp maplesat_static_6c

minisat:
	make -C simp rs

clean:
	make -C simp clean
