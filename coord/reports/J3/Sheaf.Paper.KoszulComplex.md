## What changed

Proved `ExteriorAlgebra.koszul_contract_mem` using the degree clause of
`ExteriorAlgebra.koszul_differential`, identifying the Mathlib contraction with the
unique differential by its unit and generator recursion. Proved
`ExteriorAlgebra.koszulBoundary_comp` directly from Mathlib's
`CliffordAlgebra.contractLeft_contractLeft`, and proved
`ExteriorAlgebra.koszulBoundary_rTensor_comp` using `LinearMap.rTensor_comp`.
Definitions are unchanged. Removed the public import of
`Sheaf.Paper.KoszulDifferentialSquareZero`; the import change is recorded in
`coord/changes/koszul-complex-square-zero-import.md`.

## Proved and sorry left

Closed `koszul_contract_mem`, `koszulBoundary_comp`, and
`koszulBoundary_rTensor_comp`. No `sorry` remains in `Sheaf.Paper.KoszulComplex`.

## No longer needed

Removed import and module `Sheaf.Paper.KoszulDifferentialSquareZero`, node
`lem-weil-pbc-koszul-differential-square-zero`: its only importer was KoszulComplex,
and no other library module uses its theorem. Mathlib supplies square-zero directly.
The Koszul differential, exterior powers, tensor product and homology dependencies
remain needed. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's definition node had no proof steps. The implemented proofs use the stated
Koszul differential declaration and the Mathlib contraction lemmas directly.

## Second reading by J3

1. Compared the delivered module with the repository version. Existing declaration
   signatures and definitions are unchanged; only three proofs and one public import
   changed. Verdict: pass.
2. Compiled `Sheaf.Paper.KoszulComplex` with the prescribed `lcompile.py` command.
   The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proved declarations use only the permitted kernel axioms
   together with `sorryAx` inherited from the still-open Koszul differential theorem.
   Verdict: pass.
3. Checked the three proof routes against Mathlib and the imported declarations.
   `koszul_contract_mem` uses the differential's degree clause and contraction
   recursion; the two composition results use `contractLeft_contractLeft` and
   `rTensor_comp`. No split-off statement was added, and the existing DAG node's
   proof and proof dependencies match the code. Verdict: pass.
4. Checked pruning and imports. `KoszulDifferentialSquareZero` is not used by any
   declaration or downstream module; Mathlib's contraction square-zero theorem
   replaces it. The corresponding change record is present. Verdict: pass.
5. Checked the unit record and route. The Koszul complex definition and its realized
   route remain intact; the proof only shortens the implementation below the unit
   level. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof repair
was needed.
