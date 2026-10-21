## What changed

Proved `CategoryTheory.Adjunction.tensorArrowMate_right_unit` in
`Sheaf.CategoryTheory.TensorArrowMateRightUnit` without changing its statement or imports.
The proof follows all three existing DAG steps: interchange for the tensor bifunctor,
naturality of the right action and its assumed comparison equation, then functoriality
and naturality of the adjunction unit. All ingredients are in the two existing Mathlib
imports; no intermediate project theorem is required.

## Proved and sorry left

Closed the one original hole in `CategoryTheory.Adjunction.tensorArrowMate_right_unit`
(node `lem-weil-pbc-tensor-arrow-mate-right-unit`). Both conjuncts are proved.
Zero holes remain in the delivered module; zero holes were added or split off.
The final module compiled cleanly through `lcompile.py` (Lean time 2.8 seconds).

## No longer needed

None. Both original public imports are needed by the unchanged statement. The existing
proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf and
remains represented by the imported adjunction API. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing DAG proof and the Lean statement agree, and the unit route is
preserved. Searches found stronger monoidal-category statements, but the direct proof
uses only the stated bare bifunctor and natural right-action data.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
