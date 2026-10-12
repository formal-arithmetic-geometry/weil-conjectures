## What changed
Added `Sheaf.RingTheory.KoszulConormalVectorBasisData` with a split intermediate theorem and proved `ExteriorAlgebra.exists_koszul_conormal_basis` using `Module.Basis.mk`. Updated the DAG route and removed `Sheaf.Paper.KoszulComplex`.

## Proved and sorry left
`ExteriorAlgebra.exists_koszul_conormal_basis` is proved. `ExteriorAlgebra.koszulConormalVector_linearIndependent_and_span` remains `sorry` (node `lem-sc-koszul-conormal-basis-data`).

## No longer needed
Removed proof-only import `Sheaf.Paper.KoszulComplex`.

## Where the brief, the DAG or earlier work was wrong
The exactness and tensor argument in the plan is not available in current declarations, so it is split into the strictly smaller linear-independence-and-spanning theorem.

## New nodes
`lem-sc-koszul-conormal-basis-data` records the intermediate theorem and source.

## Second reading by S1

1. Compared the delivered module with the repository version: the existing target
   signature and all declarations are byte-for-byte unchanged; only the proof and a
   proof-only import changed. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; the target has no `sorry`, and the
   only remaining `sorry` is the named split theorem. No forbidden declarations or
   hollow definitions were added. Verdict: pass.
3. Searched the library and Mathlib search services for the split theorem and target;
   no existing declaration duplicates either statement. The split theorem is the
   needed linear-independence-and-spanning reduction and is strictly smaller than the
   target, with its source and node recorded. Verdict: pass.
4. The proof uses `Module.Basis.mk` and `Module.Basis.mk_apply`, the shortest available
   route; the obsolete `Sheaf.Paper.KoszulComplex` proof import is removed. Verdict:
   pass; no further pruning found.
5. The DAG proof and dependency fields match the Lean proof, and the unit's realized
   route remains through the conormal basis node. Verdict: pass.

Changed only the proof-only import and proof, and recorded this second reading.

## Earlier second reading (a previous round; superseded)
The target proof is a direct application of the new intermediate statement and `Module.Basis.mk`; signatures are unchanged and the unit route is retained.
