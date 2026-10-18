## What changed

Proved `AlgebraicGeometry.proper_stability` in
`Sheaf.AlgebraicGeometry.ProperStability`, preserving its signature and imports.
The first two conjuncts are Mathlib's `IsProper.isStableUnderBaseChange` and
`IsProper.stableUnderComposition`. For the final conjunct, install the given
properness proof locally and use the proper pullback-second-projection instance.
This follows the existing DAG proof and its two Mathlib leaves directly.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.proper_stability`
(node `lem-kun-proper-stability`). Added 0 holes; no sorry remains in the module.
No decomposition was needed. Compiled the file through `lcompile.py`; the
initial style warning was corrected before the final compile and delivery checks.

## No longer needed

None. The sole import, `Mathlib.AlgebraicGeometry.Morphisms.Proper`, supplies both
the statement and all proof instances. Both existing proof dependencies,
`lem-weil-pbc-proper-base-change` and `lem-weil-pbc-proper-composition`, remain
used through their Mathlib declarations. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The current blueprint statement agrees with the assigned declaration.
The existing DAG plan is realized without changing the unit route or node fields.
Mathlib's instances require no additional hypotheses, including no nonemptiness
of either scheme, and the base-change projection has the required orientation.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
