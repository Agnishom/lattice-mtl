
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val id : 'a1 -> 'a1 **)

let id x =
  x

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Pervasives.succ n) m
 end

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x :: _ -> x

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a :: l0 -> rev_append l0 (a :: l')

(** val rev' : 'a1 list -> 'a1 list **)

let rev' l =
  rev_append l []

(** val repeatAux : 'a1 -> int -> 'a1 list -> 'a1 list **)

let rec repeatAux x n acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun k -> repeatAux x k (x :: acc))
    n

(** val repeat' : 'a1 -> int -> 'a1 list **)

let repeat' x n =
  repeatAux x n []

type 'a monoid = { op : ('a -> 'a -> 'a); unit0 : 'a }

type 'a lattice = { join : ('a -> 'a -> 'a); meet : ('a -> 'a -> 'a) }

type 'a boundedLattice = { bottom : 'a; top : 'a }

(** val joinMonoid :
    'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid **)

let joinMonoid _ h0 h1 =
  { op = h0.join; unit0 = h1.bottom }

(** val meetMonoid :
    'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid **)

let meetMonoid _ h0 h1 =
  { op = h0.meet; unit0 = h1.top }

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

type ('a, 'b) mealy = ('a, 'b) __mealy Lazy.t
and ('a, 'b) __mealy =
| Build_Mealy of ('a -> 'b) * ('a -> ('a, 'b) mealy)

(** val mOut : ('a1, 'a2) mealy -> 'a1 -> 'a2 **)

let mOut m =
  let Build_Mealy (mOut0, _) = Lazy.force m in mOut0

(** val mNext : ('a1, 'a2) mealy -> 'a1 -> ('a1, 'a2) mealy **)

let mNext m =
  let Build_Mealy (_, mNext0) = Lazy.force m in mNext0

(** val mCompose :
    ('a1, 'a2) mealy -> ('a2, 'a3) mealy -> ('a1, 'a3) mealy **)

let rec mCompose m n =
  lazy (Build_Mealy ((fun x -> mOut n (mOut m x)), (fun x ->
    mCompose (mNext m x) (mNext n (mOut m x)))))

(** val mLift : ('a1 -> 'a2) -> ('a1, 'a2) mealy **)

let rec mLift f =
  lazy (Build_Mealy (f, (fun _ -> mLift f)))

(** val mPar :
    ('a1, 'a2) mealy -> ('a1, 'a3) mealy -> ('a1, 'a2 * 'a3) mealy **)

let rec mPar m n =
  lazy (Build_Mealy ((fun x -> ((mOut m x), (mOut n x))), (fun x ->
    mPar (mNext m x) (mNext n x))))

(** val mBinOp :
    ('a2 -> 'a3 -> 'a4) -> ('a1, 'a2) mealy -> ('a1, 'a3) mealy -> ('a1, 'a4)
    mealy **)

let rec mBinOp op0 m n =
  lazy (Build_Mealy ((fun a -> op0 (mOut m a) (mOut n a)), (fun a ->
    mBinOp op0 (mNext m a) (mNext n a))))

(** val mFold :
    ('a2 -> 'a2 -> 'a2) -> ('a1, 'a2) mealy -> 'a2 -> ('a1, 'a2) mealy **)

let rec mFold op0 m init =
  lazy (Build_Mealy ((fun a -> op0 init (mOut m a)), (fun a ->
    mFold op0 (mNext m a) (op0 init (mOut m a)))))

type 'b queue = { front : 'b list; back : 'b list }

(** val enqueue : 'a1 -> 'a1 queue -> 'a1 queue **)

let enqueue new1 q =
  { front = q.front; back = (new1 :: q.back) }

(** val dequeue : 'a1 queue -> 'a1 queue **)

let dequeue q =
  match q.front with
  | [] ->
    (match rev' q.back with
     | [] -> { front = []; back = [] }
     | _ :: ys -> { front = ys; back = [] })
  | _ :: xs -> { front = xs; back = q.back }

(** val queueHead : 'a1 queue -> 'a1 option **)

let queueHead q =
  match q.front with
  | [] -> (match rev' q.back with
           | [] -> None
           | y :: _ -> Some y)
  | x :: _ -> Some x

(** val cycle : 'a1 -> 'a1 queue -> 'a1 queue **)

let cycle new1 q =
  dequeue (enqueue new1 q)

(** val delayWith : 'a2 queue -> ('a1, 'a2) mealy -> ('a1, 'a2) mealy **)

let rec delayWith q m =
  lazy (Build_Mealy ((fun a ->
    match queueHead q with
    | Some x -> x
    | None -> mOut m a), (fun a ->
    delayWith (cycle (mOut m a) q) (mNext m a))))

(** val delay : 'a2 -> int -> ('a1, 'a2) mealy -> ('a1, 'a2) mealy **)

let delay init n m =
  delayWith { front = (repeat' init n); back = [] } m

type 'b aggQueue = { new0 : 'b list; newAgg : 'b; oldAggs : 'b list }

(** val agg : 'a1 monoid -> 'a1 aggQueue -> 'a1 **)

let agg monoid_B q =
  match q.oldAggs with
  | [] -> q.newAgg
  | x :: _ -> monoid_B.op x q.newAgg

(** val aggEnqueue : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggEnqueue monoid_B n q =
  { new0 = (n :: q.new0); newAgg = (monoid_B.op q.newAgg n); oldAggs =
    q.oldAggs }

(** val aggStep : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggStep monoid_B q =
  match q.new0 with
  | [] -> q
  | n :: ns ->
    { new0 = ns; newAgg = monoid_B.unit0; oldAggs =
      ((monoid_B.op n (hd monoid_B.unit0 q.oldAggs)) :: q.oldAggs) }

(** val aggFlip : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let rec aggFlip monoid_B x =
  match x.new0 with
  | [] -> x
  | _ :: _ -> aggFlip monoid_B (aggStep monoid_B x)

(** val aggDequeue : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggDequeue monoid_B q =
  match q.oldAggs with
  | [] ->
    let newQ = aggFlip monoid_B q in
    (match newQ.oldAggs with
     | [] -> newQ
     | _ :: os -> { new0 = newQ.new0; newAgg = newQ.newAgg; oldAggs = os })
  | _ :: os -> { new0 = q.new0; newAgg = q.newAgg; oldAggs = os }

(** val aggCycle : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggCycle monoid_B n q =
  aggDequeue monoid_B (aggEnqueue monoid_B n q)

(** val mFoldAux :
    'a1 monoid -> 'a1 aggQueue -> ('a2, 'a1) mealy -> ('a2, 'a1) mealy **)

let rec mFoldAux monoid_B q m =
  lazy (Build_Mealy ((fun a ->
    agg monoid_B (aggCycle monoid_B (mOut m a) q)), (fun a ->
    mFoldAux monoid_B (aggCycle monoid_B (mOut m a) q) (mNext m a))))

(** val unitQueue : 'a1 monoid -> int -> 'a1 aggQueue **)

let unitQueue monoid_B n =
  { new0 = []; newAgg = monoid_B.unit0; oldAggs = (repeat' monoid_B.unit0 n) }

(** val mFoldWin :
    'a1 monoid -> int -> ('a2, 'a1) mealy -> ('a2, 'a1) mealy **)

let mFoldWin monoid_B n m =
  mFoldAux monoid_B (unitQueue monoid_B n) m

type ('val0, 'a) monitor = ('a, 'val0) mealy

(** val monAtomic : ('a2 -> 'a1) -> ('a1, 'a2) monitor **)

let monAtomic =
  mLift

(** val monAnd :
    'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor **)

let monAnd lattice_val m n =
  mBinOp lattice_val.meet m n

(** val monOr :
    'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor **)

let monOr lattice_val m n =
  mBinOp lattice_val.join m n

(** val monSometimeUnbounded :
    'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor **)

let monSometimeUnbounded lattice_val boundedLattice_val m =
  mFold lattice_val.join m boundedLattice_val.bottom

(** val monAlwaysUnbounded :
    'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor **)

let monAlwaysUnbounded lattice_val boundedLattice_val m =
  mFold lattice_val.meet m boundedLattice_val.top

(** val monDelay :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
    'a2) monitor **)

let monDelay _ boundedLattice_val n m =
  delay boundedLattice_val.bottom n m

(** val monDelayDual :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
    'a2) monitor **)

let monDelayDual _ boundedLattice_val n m =
  delay boundedLattice_val.top n m

(** val monSometimeBounded :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
    'a2) monitor **)

let monSometimeBounded lattice_val boundedLattice_val n m =
  mFoldWin (joinMonoid lattice_val lattice_val boundedLattice_val)
    (Pervasives.succ n) m

(** val monAlwaysBounded :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a2) monitor -> ('a1,
    'a2) monitor **)

let monAlwaysBounded lattice_val boundedLattice_val n m =
  mFoldWin (meetMonoid lattice_val lattice_val boundedLattice_val)
    (Pervasives.succ n) m

(** val sinceAux :
    'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> 'a1 -> ('a1,
    'a2) monitor **)

let rec sinceAux lattice_val m1 m2 pre =
  lazy (Build_Mealy ((fun a ->
    lattice_val.join (mOut m2 a) (lattice_val.meet pre (mOut m1 a))),
    (fun a ->
    sinceAux lattice_val (mNext m1 a) (mNext m2 a)
      (lattice_val.join (mOut m2 a) (lattice_val.meet pre (mOut m1 a))))))

(** val monSince :
    'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor -> ('a1, 'a2) monitor **)

let monSince lattice_val boundedLattice_val m1 m2 =
  sinceAux lattice_val m1 m2 boundedLattice_val.bottom

(** val sinceDualAux :
    'a1 lattice -> ('a1, 'a2) monitor -> ('a1, 'a2) monitor -> 'a1 -> ('a1,
    'a2) monitor **)

let rec sinceDualAux lattice_val m1 m2 pre =
  lazy (Build_Mealy ((fun a ->
    lattice_val.meet (mOut m2 a) (lattice_val.join pre (mOut m1 a))),
    (fun a ->
    sinceDualAux lattice_val (mNext m1 a) (mNext m2 a)
      (lattice_val.meet (mOut m2 a) (lattice_val.join pre (mOut m1 a))))))

(** val monSinceDual :
    'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) monitor -> ('a1, 'a2)
    monitor -> ('a1, 'a2) monitor **)

let monSinceDual lattice_val boundedLattice_val m1 m2 =
  sinceDualAux lattice_val m1 m2 boundedLattice_val.top

(** val monSinceUp :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor **)

let monSinceUp lattice_val boundedLattice_val n =
  monAnd lattice_val
    (monSince lattice_val boundedLattice_val (monAtomic fst) (monAtomic snd))
    (monSometimeBounded lattice_val boundedLattice_val n (monAtomic snd))

(** val monSinceAB :
    'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1 * 'a1)
    monitor **)

let monSinceAB lattice_val boundedLattice_val pa b =
  monAnd lattice_val
    (monDelay lattice_val boundedLattice_val (Pervasives.succ pa)
      (monSinceUp lattice_val boundedLattice_val (sub b (Pervasives.succ pa))))
    (monAlwaysBounded lattice_val boundedLattice_val pa (monAtomic fst))

(** val monSinceLo :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor **)

let monSinceLo lattice_val boundedLattice_val pa =
  monAnd lattice_val
    (monDelay lattice_val boundedLattice_val (Pervasives.succ pa)
      (monSince lattice_val boundedLattice_val (monAtomic fst)
        (monAtomic snd)))
    (monAlwaysBounded lattice_val boundedLattice_val pa (monAtomic fst))

(** val monSinceDualLo :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor **)

let monSinceDualLo lattice_val boundedLattice_val pa =
  monOr lattice_val
    (monDelayDual lattice_val boundedLattice_val (Pervasives.succ pa)
      (monSinceDual lattice_val boundedLattice_val (monAtomic fst)
        (monAtomic snd)))
    (monSometimeBounded lattice_val boundedLattice_val pa (monAtomic fst))

(** val monSinceDualUp :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1 * 'a1) monitor **)

let monSinceDualUp lattice_val boundedLattice_val n =
  monOr lattice_val
    (monSinceDual lattice_val boundedLattice_val (monAtomic fst)
      (monAtomic snd))
    (monAlwaysBounded lattice_val boundedLattice_val n (monAtomic snd))

(** val monSinceDualAB :
    'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1 * 'a1)
    monitor **)

let monSinceDualAB lattice_val boundedLattice_val pa b =
  monOr lattice_val
    (monDelayDual lattice_val boundedLattice_val (Pervasives.succ pa)
      (monSinceDualUp lattice_val boundedLattice_val
        (sub b (Pervasives.succ pa))))
    (monSometimeBounded lattice_val boundedLattice_val pa (monAtomic fst))

(** val monSometimeAB :
    'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1) monitor **)

let monSometimeAB lattice_val boundedLattice_val a b =
  monDelay lattice_val boundedLattice_val a
    (monSometimeBounded lattice_val boundedLattice_val (sub b a)
      (monAtomic id))

(** val monAlwaysAB :
    'a1 lattice -> 'a1 boundedLattice -> int -> int -> ('a1, 'a1) monitor **)

let monAlwaysAB lattice_val boundedLattice_val a b =
  monDelayDual lattice_val boundedLattice_val a
    (monAlwaysBounded lattice_val boundedLattice_val (sub b a) (monAtomic id))

(** val monSometimeLo :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1) monitor **)

let monSometimeLo lattice_val boundedLattice_val a =
  monDelay lattice_val boundedLattice_val a
    (monSometimeUnbounded lattice_val boundedLattice_val (monAtomic id))

(** val monAlwaysLo :
    'a1 lattice -> 'a1 boundedLattice -> int -> ('a1, 'a1) monitor **)

let monAlwaysLo lattice_val boundedLattice_val a =
  monDelayDual lattice_val boundedLattice_val a
    (monAlwaysUnbounded lattice_val boundedLattice_val (monAtomic id))

(** val toMonitor :
    'a1 lattice -> 'a1 boundedLattice -> ('a1, 'a2) formula -> ('a1, 'a2)
    monitor **)

let rec toMonitor lattice_val boundedLattice_val = function
| FAtomic f -> monAtomic f
| FAnd (_UU03b1_, _UU03b2_) ->
  monAnd lattice_val (toMonitor lattice_val boundedLattice_val _UU03b1_)
    (toMonitor lattice_val boundedLattice_val _UU03b2_)
| FOr (_UU03b1_, _UU03b2_) ->
  monOr lattice_val (toMonitor lattice_val boundedLattice_val _UU03b1_)
    (toMonitor lattice_val boundedLattice_val _UU03b2_)
| FSometime (a, b, _UU03b1_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monSometimeBounded lattice_val boundedLattice_val b
       (toMonitor lattice_val boundedLattice_val _UU03b1_))
     (fun _ ->
     if (=) a b
     then monDelay lattice_val boundedLattice_val a
            (toMonitor lattice_val boundedLattice_val _UU03b1_)
     else if Nat.ltb a b
          then mCompose (toMonitor lattice_val boundedLattice_val _UU03b1_)
                 (monSometimeAB lattice_val boundedLattice_val a b)
          else monAtomic (fun _ -> boundedLattice_val.bottom))
     a)
| FAlways (a, b, _UU03b1_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monAlwaysBounded lattice_val boundedLattice_val b
       (toMonitor lattice_val boundedLattice_val _UU03b1_))
     (fun _ ->
     if (=) a b
     then monDelayDual lattice_val boundedLattice_val a
            (toMonitor lattice_val boundedLattice_val _UU03b1_)
     else if Nat.ltb a b
          then mCompose (toMonitor lattice_val boundedLattice_val _UU03b1_)
                 (monAlwaysAB lattice_val boundedLattice_val a b)
          else monAtomic (fun _ -> boundedLattice_val.top))
     a)
| FSometimeUnbounded (a, _UU03b1_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monSometimeUnbounded lattice_val boundedLattice_val
       (toMonitor lattice_val boundedLattice_val _UU03b1_))
     (fun _ ->
     mCompose (toMonitor lattice_val boundedLattice_val _UU03b1_)
       (monSometimeLo lattice_val boundedLattice_val a))
     a)
| FAlwaysUnbounded (a, _UU03b1_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monAlwaysUnbounded lattice_val boundedLattice_val
       (toMonitor lattice_val boundedLattice_val _UU03b1_))
     (fun _ ->
     mCompose (toMonitor lattice_val boundedLattice_val _UU03b1_)
       (monAlwaysLo lattice_val boundedLattice_val a))
     a)
| FSince (a, b, _UU03b1_, _UU03b2_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     mCompose
       (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
         (toMonitor lattice_val boundedLattice_val _UU03b2_))
       (monSinceUp lattice_val boundedLattice_val b))
     (fun pa ->
     if Nat.ltb pa b
     then mCompose
            (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
              (toMonitor lattice_val boundedLattice_val _UU03b2_))
            (monSinceAB lattice_val boundedLattice_val pa b)
     else monAtomic (fun _ -> boundedLattice_val.bottom))
     a)
| FSinceDual (a, b, _UU03b1_, _UU03b2_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     mCompose
       (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
         (toMonitor lattice_val boundedLattice_val _UU03b2_))
       (monSinceDualUp lattice_val boundedLattice_val b))
     (fun pa ->
     if Nat.ltb pa b
     then mCompose
            (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
              (toMonitor lattice_val boundedLattice_val _UU03b2_))
            (monSinceDualAB lattice_val boundedLattice_val pa b)
     else monAtomic (fun _ -> boundedLattice_val.top))
     a)
| FSinceUnbounded (a, _UU03b1_, _UU03b2_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monSince lattice_val boundedLattice_val
       (toMonitor lattice_val boundedLattice_val _UU03b1_)
       (toMonitor lattice_val boundedLattice_val _UU03b2_))
     (fun pa ->
     mCompose
       (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
         (toMonitor lattice_val boundedLattice_val _UU03b2_))
       (monSinceLo lattice_val boundedLattice_val pa))
     a)
| FSinceDualUnbounded (a, _UU03b1_, _UU03b2_) ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     monSinceDual lattice_val boundedLattice_val
       (toMonitor lattice_val boundedLattice_val _UU03b1_)
       (toMonitor lattice_val boundedLattice_val _UU03b2_))
     (fun pa ->
     mCompose
       (mPar (toMonitor lattice_val boundedLattice_val _UU03b1_)
         (toMonitor lattice_val boundedLattice_val _UU03b2_))
       (monSinceDualLo lattice_val boundedLattice_val pa))
     a)
