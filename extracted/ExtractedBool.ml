
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

(** val joinMonoid : 'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid **)

let joinMonoid _ h0 h1 =
  { op = h0.join; unit0 = h1.bottom }

(** val meetMonoid : 'a1 lattice -> 'a1 lattice -> 'a1 boundedLattice -> 'a1 monoid **)

let meetMonoid _ h0 h1 =
  { op = h0.meet; unit0 = h1.top }

type ('val0, 'a) formula =
| FAtomic of ('a -> 'val0)
| FDelay of int * ('val0, 'a) formula
| FDelayDual of int * ('val0, 'a) formula
| FAnd of ('val0, 'a) formula * ('val0, 'a) formula
| FOr of ('val0, 'a) formula * ('val0, 'a) formula
| FSometime of ('val0, 'a) formula
| FAlways of ('val0, 'a) formula
| FSince of ('val0, 'a) formula * ('val0, 'a) formula
| FSinceDual of ('val0, 'a) formula * ('val0, 'a) formula
| FAlwaysWithin of int * ('val0, 'a) formula
| FSometimeWithin of int * ('val0, 'a) formula

(** val fPre : ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fPre _UU03d5_ =
  FDelay (0, _UU03d5_)

(** val fSometimeBounded : int -> int -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSometimeBounded lo len _UU03d5_ =
  FDelay (lo, (FSometimeWithin (len, _UU03d5_)))

(** val fAlwaysBounded : int -> int -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fAlwaysBounded lo len _UU03d5_ =
  FDelayDual (lo, (FAlwaysWithin (len, _UU03d5_)))

(** val fSinceWithin : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceWithin hi _UU03d5_ _UU03c8_ =
  FAnd ((FDelay (hi, _UU03c8_)), (FSince (_UU03d5_, _UU03c8_)))

(** val fSinceBounded : int -> int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceBounded lo len _UU03d5_ _UU03c8_ =
  FAnd ((FAlwaysWithin (lo, _UU03d5_)), (FDelay ((Pervasives.succ lo),
    (fSinceWithin len _UU03d5_ _UU03c8_))))

(** val fSinceAfter : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceAfter lo _UU03d5_ _UU03c8_ =
  FDelay (lo, (FSince (_UU03d5_, _UU03c8_)))

(** val fSinceWithinDual : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceWithinDual hi _UU03d5_ _UU03c8_ =
  FOr ((FDelayDual (hi, _UU03c8_)), (FSinceDual (_UU03d5_, _UU03c8_)))

(** val fSinceBoundedDual :
    int -> int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceBoundedDual lo len _UU03d5_ _UU03c8_ =
  FOr ((FSometimeWithin (lo, _UU03d5_)), (FDelayDual ((Pervasives.succ lo),
    (fSinceWithin len _UU03d5_ _UU03c8_))))

(** val fSinceAfterDual : int -> ('a1, 'a2) formula -> ('a1, 'a2) formula -> ('a1, 'a2) formula **)

let fSinceAfterDual lo _UU03d5_ _UU03c8_ =
  FDelayDual (lo, (FSinceDual (_UU03d5_, _UU03c8_)))

type ('a, 'b) moore = ('a, 'b) __moore Lazy.t
and ('a, 'b) __moore =
| Build_Moore of 'b * ('a -> ('a, 'b) moore)

(** val mOut : ('a1, 'a2) moore -> 'a2 **)

let mOut m =
  let Build_Moore (mOut0, _) = Lazy.force m in mOut0

(** val mNext : ('a1, 'a2) moore -> 'a1 -> ('a1, 'a2) moore **)

let mNext m =
  let Build_Moore (_, mNext0) = Lazy.force m in mNext0

(** val mNextOut : ('a1, 'a2) moore -> 'a1 -> 'a2 **)

let mNextOut m a =
  mOut (mNext m a)

(** val mLift : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) moore **)

let rec mLift f init =
  lazy (Build_Moore (init, (fun a -> mLift f (f a))))

(** val delayyWith : 'a2 -> 'a2 list -> 'a2 list -> ('a1, 'a2) moore -> ('a1, 'a2) moore **)

let rec delayyWith init front back m =
  lazy (Build_Moore (init, (fun a ->
    match front with
    | [] ->
      let back' = rev' back in
      (match back' with
       | [] -> delayyWith (mOut m) [] [] (mNext m a)
       | b :: bs -> delayyWith b bs ((mOut m) :: []) (mNext m a))
    | f :: fs -> delayyWith f fs ((mOut m) :: back) (mNext m a))))

(** val mBinOp : ('a2 -> 'a3 -> 'a4) -> ('a1, 'a2) moore -> ('a1, 'a3) moore -> ('a1, 'a4) moore **)

let rec mBinOp op0 m1 m2 =
  lazy (Build_Moore ((op0 (mOut m1) (mOut m2)), (fun a -> mBinOp op0 (mNext m1 a) (mNext m2 a))))

(** val mFoldAux : 'a1 monoid -> ('a2, 'a1) moore -> 'a1 -> ('a2, 'a1) moore **)

let rec mFoldAux monoid_B m st =
  lazy (Build_Moore (st, (fun a -> mFoldAux monoid_B (mNext m a) (monoid_B.op st (mNextOut m a)))))

(** val mFold : 'a1 monoid -> ('a2, 'a1) moore -> ('a2, 'a1) moore **)

let mFold monoid_B m =
  mFoldAux monoid_B m (mOut m)

type 'b aggQueue = { ff : ('b * 'b) list; rr : ('b * 'b) list }

(** val aggrr : 'a1 monoid -> 'a1 aggQueue -> 'a1 **)

let aggrr monoid_B q =
  match q.rr with
  | [] -> monoid_B.unit0
  | p :: _ -> let (xa, _) = p in xa

(** val aggff : 'a1 monoid -> 'a1 aggQueue -> 'a1 **)

let aggff monoid_B q =
  match q.ff with
  | [] -> monoid_B.unit0
  | p :: _ -> let (ya, _) = p in ya

(** val aggOut : 'a1 monoid -> 'a1 aggQueue -> 'a1 **)

let aggOut monoid_B q =
  monoid_B.op (aggff monoid_B q) (aggrr monoid_B q)

(** val aggStep : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggStep monoid_B q =
  match q.rr with
  | [] -> q
  | p :: rs -> let (_, r) = p in { ff = (((monoid_B.op r (aggff monoid_B q)), r) :: q.ff); rr = rs }

(** val aggFlip : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let rec aggFlip monoid_B x =
  match x.rr with
  | [] -> x
  | _ :: _ -> aggFlip monoid_B (aggStep monoid_B x)

(** val aggEnQ : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggEnQ monoid_B new0 q =
  { ff = q.ff; rr = (((monoid_B.op (aggrr monoid_B q) new0), new0) :: q.rr) }

(** val aggDQ : 'a1 monoid -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggDQ monoid_B q =
  match q.ff with
  | [] ->
    let newQ = aggFlip monoid_B q in
    (match newQ.ff with
     | [] -> newQ
     | _ :: fs -> { ff = fs; rr = newQ.rr })
  | _ :: fs -> { ff = fs; rr = q.rr }

(** val aggCycle : 'a1 monoid -> 'a1 -> 'a1 aggQueue -> 'a1 aggQueue **)

let aggCycle monoid_B x q =
  aggDQ monoid_B (aggEnQ monoid_B x q)

(** val initAggQ : 'a1 monoid -> int -> 'a1 aggQueue **)

let initAggQ monoid_B n =
  { ff = (repeat' (monoid_B.unit0, monoid_B.unit0) (Pervasives.succ n)); rr = [] }

(** val mWinFoldAux : 'a1 monoid -> 'a1 aggQueue -> ('a2, 'a1) moore -> ('a2, 'a1) moore **)

let rec mWinFoldAux monoid_B qq m =
  lazy (Build_Moore ((monoid_B.op (aggOut monoid_B qq) (mOut m)), (fun a ->
    mWinFoldAux monoid_B (aggCycle monoid_B (mOut m) qq) (mNext m a))))

(** val mWinFold : 'a1 monoid -> ('a2, 'a1) moore -> int -> ('a2, 'a1) moore **)

let mWinFold monoid_B m n =
  mWinFoldAux monoid_B (initAggQ monoid_B n) m

type val0 = bool

(** val lattice_val : val0 lattice **)

let lattice_val = {join = (||); meet = (&&); }

(** val boundedLattice_val : val0 boundedLattice **)

let boundedLattice_val = {top = true; bottom = false; }

type 'a monitor = ('a, val0) moore

(** val monLift : ('a1 -> val0) -> 'a1 monitor **)

let monLift f =
  mLift f boundedLattice_val.bottom

(** val mDelay : int -> 'a1 monitor -> 'a1 monitor **)

let mDelay n m =
  delayyWith boundedLattice_val.bottom (repeat' boundedLattice_val.bottom n) [] m

(** val mDelayDual : int -> 'a1 monitor -> 'a1 monitor **)

let mDelayDual n m =
  delayyWith boundedLattice_val.top (repeat' boundedLattice_val.top n) [] m

(** val mAnd : 'a1 monitor -> 'a1 monitor -> 'a1 monitor **)

let mAnd m1 m2 =
  mBinOp lattice_val.meet m1 m2

(** val mOr : 'a1 monitor -> 'a1 monitor -> 'a1 monitor **)

let mOr m1 m2 =
  mBinOp lattice_val.join m1 m2

(** val mSometime : 'a1 monitor -> 'a1 monitor **)

let mSometime m =
  mFold (joinMonoid lattice_val lattice_val boundedLattice_val) m

(** val mAlways : 'a1 monitor -> 'a1 monitor **)

let mAlways m =
  mFold (meetMonoid lattice_val lattice_val boundedLattice_val) m

(** val sinceAux : 'a1 monitor -> 'a1 monitor -> val0 -> 'a1 monitor **)

let rec sinceAux m1 m2 pre =
  lazy (Build_Moore (pre, (fun a ->
    sinceAux (mNext m1 a) (mNext m2 a)
      (lattice_val.join (mNextOut m2 a) (lattice_val.meet (mNextOut m1 a) pre)))))

(** val since : 'a1 monitor -> 'a1 monitor -> 'a1 monitor **)

let since m1 m2 =
  sinceAux m1 m2 (mOut m2)

(** val sinceDualAux : 'a1 monitor -> 'a1 monitor -> val0 -> 'a1 monitor **)

let rec sinceDualAux m1 m2 pre =
  lazy (Build_Moore (pre, (fun a ->
    sinceDualAux (mNext m1 a) (mNext m2 a)
      (lattice_val.meet (mNextOut m2 a) (lattice_val.join (mNextOut m1 a) pre)))))

(** val sinceDual : 'a1 monitor -> 'a1 monitor -> 'a1 monitor **)

let sinceDual m1 m2 =
  sinceDualAux m1 m2 (mOut m2)

(** val mAlwaysWithin : int -> 'a1 monitor -> 'a1 monitor **)

let mAlwaysWithin hi m =
  mWinFold (meetMonoid lattice_val lattice_val boundedLattice_val) m hi

(** val mSometimeWithin : int -> 'a1 monitor -> 'a1 monitor **)

let mSometimeWithin hi m =
  mWinFold (joinMonoid lattice_val lattice_val boundedLattice_val) m hi

(** val toMonitor : (val0, 'a1) formula -> 'a1 monitor **)

let rec toMonitor = function
| FAtomic g -> monLift g
| FDelay (n, g) -> mDelay n (toMonitor g)
| FDelayDual (n, g) -> mDelayDual n (toMonitor g)
| FAnd (g, h) -> mAnd (toMonitor g) (toMonitor h)
| FOr (g, h) -> mOr (toMonitor g) (toMonitor h)
| FSometime g -> mSometime (toMonitor g)
| FAlways g -> mAlways (toMonitor g)
| FSince (g, h) -> since (toMonitor g) (toMonitor h)
| FSinceDual (g, h) -> sinceDual (toMonitor g) (toMonitor h)
| FAlwaysWithin (hi, g) -> mAlwaysWithin hi (toMonitor g)
| FSometimeWithin (hi, g) -> mSometimeWithin hi (toMonitor g)
