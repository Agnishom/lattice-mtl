CC=gcc#
CXX=g++#
CXXFLAGS=-std=c++11 -fPIC -O2 -pthread
CXXFLAGS_APPS=-std=c++17 -fPIC -pthread -O2 -s -DNDEBUG#-Wall -Wextra
CXXFLAGS_TEST=-g -std=c++11 -fPIC -O0 -pthread --coverage -fno-inline -fno-inline-small-functions -fno-default-inline -fvisibility=hidden#-Wall -Wextra

.PHONY: lattice-mtl semiring-monitor reelay

lattice-mtl:
	cd lattice-mtl && rm -f *.mli *.o *.cmx *.cmi
	cd lattice-mtl && ocamlopt -o lattice-mtl.bin -I ../../../extracted/ unix.cmxa ../../../extracted/LatticeMtl.ml Experiments.ml

semiring-monitor:
	cd semiring-monitor && rustc -o semiring-monitor.bin -O experiments.rs --extern signal_monitor=lib_signal_monitor_2020_10_12_1321.rlib

reelay:
	cd reelay && $(CXX) $(CXXFLAGS) experiments.cpp -o reelay.bin -I./include -lcudd
