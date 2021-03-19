Using `LatticeMtl.ml` as a library
---

Here is a step by step tutorial on how to use the `LatticeMtl.ml` file as a library for monitoring.

1. Import the library, `open LatticeMtl;;`
2. Decide the lattice `lat` you want to use. This is just a type.
   - Provide a record: `latL : { join : (lat -> lat -> lat); meet : (lat -> lat -> lat) }`
   - Provide another record: `latB : { bottom : lat; top : lat }`
3. Decide the type `sample` from which your traces are created.
4. Find atomic predicates `sample -> float` as necessary.
5. Create a formula `form : (float, sample) formula` using the constructors for formulas.
6. Your monitor is now `mon = toMonitor latL latB form`

The `mon` produced above is a coinductive object with methods `mOut` or `mNext`. `(mOut mon inp)` will produce the output of the monitor for the input `inp`. `mon' = (mNext mon inp)` will produce an updated monitor `mon'` whose state has been updated accordingly.

Example of this style of usages for the lattice of boolean values and floating points can be found in `Examples.ml`.

### Formula Constructors

Here is a list of the constructors for the formulas:

```
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
```

Details about the semantics can be found in `../src/Semantics/InfRobustness.v`.
