## What changed

Proved `DerivedCategory.isDerivedComplete_of_isDerivedLimit_of_nilpotent` in
`Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete`, preserving its entire signature.
For each level, induction computes the powers of the constant-tower shift after each
projection. Nilpotence of scalar multiplication then implies nilpotence of the shift.
Mathlib's `IsNilpotent.isUnit_one_sub` makes the Roos map invertible, and
`Pretriangulated.Triangle.isZero₁_of_isIso₂` proves the limit is zero. The existing
`DerivedCategory.isDerivedComplete_products_and_triangles` then supplies completeness
of the product and of the given derived limit.

Added the proof-only import `Mathlib.RingTheory.Nilpotent.Basic`. Updated the existing
DAG node's proof, proof dependencies and proof origin to match the implemented route.
No definitions, statements, public imports, or consumers changed. The unit's realized
statement and steps are preserved.

Validation: the delivered module compiled successfully through `lcompile.py` in 2.6 s.
The argument uses an arbitrary ideal, arbitrary unbounded objects, and exponents that
vary with both the scalar and the level. Zero objects, the zero ideal, and the trivial
ring require no extra cases. No arbitrary witnesses are used to define data.

## Proved and sorry left

Closed the single hole in
`DerivedCategory.isDerivedComplete_of_isDerivedLimit_of_nilpotent`
(node `lem-weil-pbc-nilpotent-torsion-derived-limit-complete`).
The item contains zero remaining holes. Zero holes were added and zero statements
were split off. This is a proof from the existing closure declaration, whose own
`DerivedCategory.isDerivedComplete_products_and_triangles` remains an existing
proof dependency with `sorry`; that dependency was not changed in this delivery.

## No longer needed

Removed the proof-only import
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence` and the corresponding
node dependency `lem-weil-derived-limit-existence`. The input already supplies the
product of the original tower. For each constant tower, the completeness definition
quantifies over its product structure and derived-limit triangles. Neither existence
nor uniqueness of a derived limit is needed in this proof. The closure lemma's own
proof dependencies are unaffected; this is pruning from this item, not a claim that
the existence module becomes globally unreachable.

Removed the redundant proof-only import
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: the unchanged public import
`Sheaf.CategoryTheory.Triangulated.DerivedLimit` already exports its definitions.
The node `def-weil-derived-limit` remains needed. All other original dependency nodes
remain in the proof route; `def-weil-tower-transition-endomorphism` is now explicitly
listed because its shift construction is used.

The already proved source lemma
`Pretriangulated.isIso_sub_towerShift_of_eq_zero` was considered, but translating
between its functor-indexed tower and this module's sequence would be longer than
the projection induction. Its module was not imported.

## Where the brief, the DAG or earlier work was wrong

There is no statement defect. The original plan's first step establishes existence
and uniqueness that the theorem does not need. Mathlib already proves the geometric
inverse and the distinguished-triangle zero-object consequence, so these do not need
new project lemmas. The old docstring's longer proof sketch remains valid; the node
and this report record the shorter implemented argument.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
