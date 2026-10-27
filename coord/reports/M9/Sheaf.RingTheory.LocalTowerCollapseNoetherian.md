## What changed

Proved `Module.local_tower_collapse_noetherian` in
`Sheaf.RingTheory.LocalTowerCollapseNoetherian`, with all nine conclusions and
all supplied diagrams, cocones and hypotheses unchanged. Added a proved private
wrapper `RingHom.isTensorLocalizationSquare_comp` to convert the ring-hom
localization-square predicate to the algebra structures required by the existing
proved `Module.tensorLocalization_tower_transition` theorem and back.

The Noetherian clauses use `Algebra.EssFiniteType.isNoetherianRing` over the
integers and then successively over the two stage rings. The composite
factorization uses a finite type subalgebra from Mathlib's essential-finiteness
criterion, upgraded to finite presentation over the Noetherian base. The final
four clauses apply Mathlib's concrete filtered-colimit representative and equality
theorems, converting arrows in a preorder into inequalities. Updated the node's
proof text and origin to describe this implementation; its dependency list and
unit route stay intact.

## Proved and sorry left

Closed 1 of 1 holes: `Module.local_tower_collapse_noetherian`
(node `lem-trf-local-tower-collapse-noetherian`). Added 0 holes; split off 0.
The private wrapper is completely proved. No `sorry` remains in the delivery.

## No longer needed

Removed the redundant private import `Mathlib.RingTheory.FiniteType`; its needed
results are already available through the retained imports. No DAG dependency,
module, upstream declaration, or approved tool use is pruned: the convenience
Noetherian theorem uses both recorded permanence results, and the same
composition, finite-presentation, tensor-localization and colimit leaves implement
the existing plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original proof text expanded the
integer principal-ideal proof and the two Noetherian permanence steps explicitly;
Mathlib already supplies these. Locality of the maps, the compatibility equations,
and the middle cocone's colimit property are stronger hypotheses than this
assembly requires, so the proof retains the original signature and suppresses the
unused-variable linter only for this theorem. The two tensor-localization
hypotheses already carry the pure-tensor formulas needed by the tower theorem.

Validation: the final single-file `lcompile.py` run compiled cleanly with no
warnings in 4.9 seconds. The delivery tool performs the independent axiom probe
and packet checks before pushing.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
