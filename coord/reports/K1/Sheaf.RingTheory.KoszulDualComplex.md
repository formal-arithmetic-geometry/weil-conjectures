## What changed

Proved `ExteriorAlgebra.koszulDualBoundary_comp` in the target module. The proof uses extensionality, unfolds `koszulDualBoundary`, and simplifies to the square-zero identity for the Koszul boundary. Updated the sandbox node proof and proof dependency accordingly.

## Proved and sorry left

Closed `ExteriorAlgebra.koszulDualBoundary_comp` (node `def-sc-koszul-dual-complex`). No `sorry` remains in the item module.

## No longer needed

`Mathlib.CategoryTheory.Linear.Yoneda` was unused and was removed. No DAG node or module is
otherwise obsolete.

## Where the brief, the DAG or earlier work was wrong

None.

## Second reading by K1

1. Compared the delivered module with the repository version. All existing declarations and
   signatures are byte-for-byte unchanged; only the proof of
   `ExteriorAlgebra.koszulDualBoundary_comp` and an unused import were changed.
2. Compiled the module with `lcompile.py`; the proof has no local `sorry`, forbidden declaration,
   or hollow definition. The axiom check reports only the permitted axioms plus the upstream
   `sorryAx` in the still-open Koszul-complex dependency.
3. The existing target statement and the boundary-square statement are unchanged and true: after
   extensionality, simplification reduces the composite to the Koszul differential square-zero
   identity. No new statements or nodes were added.
4. The proof follows the unit route through the recorded Koszul complex and its square-zero
   differential; no unit statement or route was bypassed.
5. The node proof and `proof_deps` agree with the Lean proof and retain the Koszul-complex
   dependency. The unused public `Mathlib.CategoryTheory.Linear.Yoneda` import was removed;
   `Mathlib.Algebra.Homology.Embedding.Extend` remains required by `koszulDualCochainComplex`.

Changed in this reading: removed the unused Yoneda import and documented the checks above.
The import change is recorded in `coord/changes/KoszulDualComplex-imports.md`.

## New nodes

None.
