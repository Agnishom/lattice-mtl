
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val id : 'a1 -> 'a1

val sub : int -> int -> int

module Nat :
 sig
  val ltb : int -> int -> bool
 end

val hd : 'a1 -> 'a1 list -> 'a1

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val rev' : 'a1 list -> 'a1 list

val repeatAux : 'a1 -> int -> 'a1 list -> 'a1 list

val repeat' : 'a1 -> int -> 'a1 list

type 'a monoid = { op : ('a -> 'a -> 'a); unit0 : 'a }

type 'a lattice = { join : ('a -> 'a -> 'a); meet : ('a -> 'a -> 'a) }

type 'a boundedLattice = { bottom : 'a; top : 'a }

val joinMonoid :
  'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid

val meetMonoid :
  'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid

type ('val0, 'a) formula =
| FAtomic of ('a -> 'val0)
| FAnd of ('val0, 'a) formula * ('val0, 'a) formula
| FOr of ('val0, 'a) formula * ('val0, 'a) formula
| FSometime of int * int * ('val0, 'a) formula
| FAlways of int * int * ('val0, 'a) formula
| FSometimeUnbounded of int * ('val0, 'a) formula
| FAlwaysUnbounded of int * ('val0, 'a) formula
| FSince of int * int * ('val0, 'a) formula * ('val0, 'a) formula
| FSinceDual of int * int * ('val0, 'a) formula * ('val0, 'a) formula
| FSinceUnbounded of int * ('val0, 'a) formula * ('val0, 'a) formula
| FSinceDualUnbounded of int * ('val0, 'a) formula * ('val0, 'a) formula

val fDelay : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula

val fDelayDual : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula

type ('a, 'b) mealy = ('a, 'b) __mealy Lazy.t
and ('a, 'b) __mealy =
| Build_Mealy of ('a -> 'b) * ('a -> ('a, 'b) mealy)

val mOut : ('a1, 'a2) mealy -> 'a1 -> 'a2

val mNext : ('a1, 'a2) mealy -> 'a1 -> ('a1, 'a2) mealy

val mCompose : ('a1, 'a2) mealy -> ('a2, 'a3) mealy -> ('a1, 'a3) mealy

val mLift : ('a1 -> 'a2) -> ('a1, 'a2) mealy

val mPar : ('a1, 'a2) mealy -> ('a1, 'a3) mealy -> ('a1, 'a2 * 'a3) mealy

val mBinOp :
  ('a2 -> 'a3 -> 'a4) -> ('a1, 'a2) mealy -> ('a1, 'a3) mealy -> ('a1, 'a4)
  mealy

val mFold : ('a2 -> 'a2 -> 'a2) -> ('a1, 'a2) mealy -> 'a2 -> ('a1, 'a2) mealy

type 'b queue = { front : 'b list; back : 'b list }

val enqueue : 'a1 -> 'a1 queue -> 'a1 queue

val dequeue : 'a1 queue -> 'a1 queue

val queueHead : 'a1 queue -> 'a1 option

val cycle : 'a1 -> 'a1 queue -> 'a1 queue

val delayWith : 'a2 queue -> ('a1, 'a2) mealy -> ('a1, 'a2) mealy

val delay : 'a2 -> int -> ('a1, 'a2) mealy -> ('a1, 'a2) mealy

type 'b aggQueue = { new0 : 'b list; newAgg : 'b; oldAggs : 'b list }

val agg : 'a1 monoid -> 'a1 aggQueue -> 'a1

val aggEnqueue : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue

val aggStep : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue

val aggFlip : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue

val aggDequeue : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue

val aggCycle : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue

val mFoldAux :
  'a1 monoid -> 'a1 aggQueue -> ('a2, 'a1) mealy -> ('a2, 'a1) mealy

val unitQueue : 'a1 monoid -> int -> 'a1 aggQueue

val mFoldWin : 'a1 monoid -> int -> ('a2, 'a1) mealy -> ('a2, 'a1) mealy

type ('val0, 'a) monitor = ('a, 'val0) mealy

val monAtomic : ('a2 -> 'a1) -> ('a1, 'a2) monitor

val monAnd :
  'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor

val monOr :
  'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor

val monSometimeUnbounded :
  'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor

val monAlwaysUnbounded :
  'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor

val monDelay :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
  'a2) monitor

val monDelayDual :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
  'a2) monitor

val monSometimeBounded :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
  'a2) monitor

val monAlwaysBounded :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
  'a2) monitor

val sinceAux :
  'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> 'a1 -> ('a1,
  'a2) monitor

val monSince :
  'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor -> ('a1, 'a2) monitor

val sinceDualAux :
  'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> 'a1 -> ('a1,
  'a2) monitor

val monSinceDual :
  'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
  monitor -> ('a1, 'a2) monitor

val monSinceUp :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor

val monSinceAB :
  'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1 * 'a1) monitor

val monSinceLo :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor

val monSinceDualLo :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor

val monSinceDualUp :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor

val monSinceDualAB :
  'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1 * 'a1) monitor

val monSometimeAB :
  'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1) monitor

val monAlwaysAB :
  'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1) monitor

val monSometimeLo :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1) monitor

val monAlwaysLo :
  'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1) monitor

val toMonitor :
  'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) formula -> ('a1, 'a2)
  monitor
