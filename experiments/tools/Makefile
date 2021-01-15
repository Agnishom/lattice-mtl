.PHONY: lattice-mtl semiring-monitor

lattice-mtl:
	cd lattice-mtl && rm -f *.mli *.o *.cmx *.cmi
	cd lattice-mtl && ocamlopt -o lattice-mtl.bin -I ../../../extracted/ unix.cmxa ../../../extracted/LatticeMtl.ml Experiments.ml

semiring-monitor:
	cd semiring-monitor && rustc -o semiring-monitor.bin -O experiments.rs --extern signal_monitor=lib_signal_monitor_2020_10_12_1321.rlib
