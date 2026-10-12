## What changed
Split the proof into two strict intermediate theorems in new modules, then proved the target by applying them and assembling their conclusions. The target now imports `SmoothAtPrimeConormalData` and `SmoothAtPrimeDifferentialData`.

## Proved and sorry left
The target theorem `Algebra.exists_smoothAtPrime_free_conormal_basis` is proved by a real Lean composition. The new declarations `Algebra.exists_smoothAtPrime_conormal_data` and `Algebra.exists_smoothAtPrime_differential_data` remain sorry, with DAG nodes `lem-weil-pbc-smooth-at-prime-free-conormal-basis-conormal-data` and `lem-weil-pbc-smooth-at-prime-free-conormal-basis-differential-data`.

## No longer needed
None; all original proof-dependency imports remain available for the intermediate statements.

## Where the brief, the DAG or earlier work was wrong
The four-step proof plan is sound but too large to close directly in this worker interval, so it was decomposed into its conormal and differential localization components.

## New nodes
The decomposition node `lem-weil-pbc-smooth-at-prime-free-conormal-basis-conormal-data` records the conormal component and its module under `lean/Sheaf/RingTheory/`. The decomposition node `lem-weil-pbc-smooth-at-prime-free-conormal-basis-differential-data` records the differential component and its module under `lean/Sheaf/RingTheory/`.

## Earlier second reading (a previous round; superseded)
The target composition is checked by compiling all three modules. The two new statements are strict parts of the original conclusion and retain the unit route; their proofs remain explicit stage-3 holes recorded by the new nodes.

## Second reading by U2

1. I compared the delivered target module with the repository version. The target
statement is byte-for-byte unchanged; only its proof and proof-only imports changed.
Verdict: pass.

2. All three delivered Lean modules compile with `lcompile.py`. The target has no
`sorry`; the two named decomposition theorems retain their documented `sorry`s and
are the only holes added. No forbidden declarations or hollow definitions occur.
Verdict: pass.

3. The original differential split was too strong: arbitrary `V,c` and smoothness
cannot determine the differential rank. I repaired it by requiring the conormal basis
witness produced by the conormal split. This is a true strict component of the
source argument and is exactly what the target proof supplies. The conormal split
itself remains a strict component with its source and node.
Verdict: repaired and pass.

4. The proof follows the unit route through the conormal and differential components.
The target no longer needs `PrescribedResidueBasisSpreads` or
`SmoothLocalizationConormalSplit` directly; those imports were removed and the target
node proof dependencies now name the two decomposition nodes. Verdict: pass.

5. The DAG now matches the repaired Lean signatures and proof dependencies. The unit
route is retained, and the target statement and definitions are unchanged.
Verdict: pass.

Changed the differential split signature and docstring, updated both affected DAG
proof records, removed two unused proof imports from the target, and recorded this
second reading.
