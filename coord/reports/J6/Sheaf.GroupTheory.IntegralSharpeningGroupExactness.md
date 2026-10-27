## What changed

Proved `AlgebraicGeometry.FineFan.integral_sharpening_group_exactness` in
`Sheaf.GroupTheory.IntegralSharpeningGroupExactness` without changing its statement.
The unit subgroup is the range of the explicit homomorphism from `Pˣ` to the
Grothendieck group. Quotient induction constructs the sharpening embedding;
extending this embedding proves integrality. Fractions prove surjectivity and
the kernel equation. Two monoid-closure inductions prove the generator clauses.
Two private, fully proved helpers give the lift equation and fraction presentation.

Replaced the two public geometry imports by the three Mathlib modules supplying
Associates, group completion and quotient groups. Updated the item's node proof
and removed its geometric proof dependencies; statement dependencies stay intact.
The interface change record is
`coord/changes/J6-integral-sharpening-group-exactness-imports.md`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.FineFan.integral_sharpening_group_exactness`
(node `lem-trf-integral-sharpening-group-exactness`).
Added zero holes; zero sorries remain in the delivered Lean module.
The private helpers `lift_of` and `exists_fraction` are proved in full.

Validation: `lcompile.py` compiled the final Lean module successfully in 2.7 s
with no warnings. The required delivery tool runs the axiom probe and preflight.
The public theorem's signature text is verbatim preserved.

## No longer needed

Removed public imports `Sheaf.AlgebraicGeometry.FineFanBlowup` and
`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`. The proof needs no fine-fan,
log-scheme, sheaf, chart or blowup constructions, only the Mathlib monoid notions
already used in its statement. Accordingly the node no longer has
`def-trf-fine-fan-blowup` or `def-trf-fs-log-blowup` as proof dependencies.
Their statement-dependency citations remain, since they explain the paper's
terminology. These modules and nodes may still be needed elsewhere in the project;
this delivery withdraws none of them.

The shared source has zero direct Lean importers and zero downstream modules for
this item (`tools/downstream.py` and an exact import-line search). Thus no consumer
adaptation or importer compilation is required for this import pruning.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's five steps can all be implemented directly
using Mathlib: no additional statement or sorry is necessary. The assigned unit's
realized statement and step lists are empty, and no unit-level route is bypassed.
Edge cases require no added assumptions: groups and torsion units are handled by
the unit range, no finite generation is used before the final implication, and
closure induction covers an empty generating list as well.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
