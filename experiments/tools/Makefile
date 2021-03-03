CC=gcc#
CXX=g++#
CXXFLAGS=-std=c++11 -fPIC -O2 -pthread
CXXFLAGS_APPS=-std=c++17 -fPIC -pthread -O2 -s -DNDEBUG#-Wall -Wextra
CXXFLAGS_TEST=-g -std=c++11 -fPIC -O0 -pthread --coverage -fno-inline -fno-inline-small-functions -fno-default-inline -fvisibility=hidden#-Wall -Wextra

.PHONY: lattice-mtl semiring-monitor reelay

lattice-mtl:
	cd lattice-mtl && rm -f *.mli *.o *.cmx *.cmi
	cd lattice-mtl && ocamlopt -o lattice-micro.bin -I ../../../extracted/ unix.cmxa ../../../extracted/LatticeMtl.ml Microbenchmarks.ml
	cd lattice-mtl && rm -f *.mli *.o *.cmx *.cmi
	cd lattice-mtl && ocamlopt -o lattice-timescales.bin -I ../../../extracted/ unix.cmxa ../../../extracted/LatticeMtl.ml Timescales.ml

semiring-monitor:
	cd semiring-monitor && rustc -o semiring-micro.bin -O microbenchmarks.rs --extern signal_monitor=lib_signal_monitor_2020_10_12_1321.rlib
	cd semiring-monitor && rustc -o semiring-timescales.bin -O timescales.rs --extern signal_monitor=lib_signal_monitor_2020_10_12_1321.rlib


reelay:
	cd reelay && $(CXX) $(CXXFLAGS) microbenchmarks.cpp -o reelay-micro.bin -I./include -lcudd
	cd reelay && $(CXX) $(CXXFLAGS) timescales.cpp -o reelay-timescales.bin -I./include -lcudd
