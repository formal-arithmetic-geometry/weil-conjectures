## What changed

In `Sheaf/AlgebraicGeometry/ModuleFinitePresentationCokernel.lean`, proved
`isFinitePresentation_cokernel_of_both_isFinitePresentation` by applying
`isFinitePresentation_cokernel_of_isFiniteType`. Mathlib's existing instance
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` supplies the finite-type
instance for `G`.

## Proved and sorry left

Closed `isFinitePresentation_cokernel_of_both_isFinitePresentation`.
`isFinitePresentation_cokernel_of_isFiniteType` remains `sorry` (node
`lem-weil-pbc-module-finite-presentation-cokernel`). No new sorries were added.

## No longer needed

No imports or DAG dependencies were removed; the proof uses the existing
finite-presentation-to-finite-type instance and the first theorem.

## Where the brief, the DAG or earlier work was wrong

No errors found.

## Second reading by P2

1. Compared the delivered module with the repository version. The existing declarations and
   signatures are byte-for-byte unchanged; only the proof of the special-case theorem changed.
   Verdict: pass.
2. Compiled the module with `lcompile.py`. There are no errors, forbidden declarations, or
   additional `sorry`s; the remaining `sorry` is the named theorem
   `isFinitePresentation_cokernel_of_isFiniteType`. The special-case proof uses the existing
   finite-presentation-to-finite-type instance and the general theorem exactly as stated.
   Verdict: pass.
3. Checked the theorem statement and searched the repository and Mathlib for an existing
   duplicate. The statement is unchanged, true, and no new split-off statement was introduced.
   Verdict: pass.
4. The shortest available route is the existing Mathlib instance followed by the general
   theorem. No import is unused as a result of this proof, and the unit route is retained.
   Verdict: pass.
5. The node's Lean declaration, proof dependency, and proof origin remain consistent with the
   source module; no DAG node changes are needed.
   Verdict: pass.

Changed only the special-case proof and added this second-reading record; no imports, statements,
definitions, or DAG dependencies were changed.
