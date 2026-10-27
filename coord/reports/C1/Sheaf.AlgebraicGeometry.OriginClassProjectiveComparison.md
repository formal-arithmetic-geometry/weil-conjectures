## What changed

Replaced the hole in `AlgebraicGeometry.Etale.origin_class_projective_comparison`
by a complete assembly from two strictly smaller geometric steps. The existing
`OriginProjectiveComparison` record and theorem signature are unchanged.

`OriginBoundaryCounitData` supplies normalized Cartier boundaries, canonical restriction,
and the actual counit square and its invertible source counit. It makes no Chern or
compact-source normalization assertion. `OriginProjectiveNormalization` supplies the
positive divisor/Chern and section-one normalization for fixed boundary data; it neither
constructs those boundary data nor assumes the final compact-image equation.
The private generic functor calculation applies sections to the counit square and uses
the two normalization equations to prove that final equation. This implication is proved
in Lean rather than being included among the new hypotheses.

The generic predicate `originNormalizationEquations` shares the category instances of its
two equations. This avoids repeated reduction of the concrete derived-category instances.
No change to `OriginComparisonArrows` is included: the earlier proposed definition repair
is retained only in ignored scratch material. New modules use public imports for their
statements; the parent uses a private proof import of the normalization module.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Etale.origin_class_projective_comparison`
(node `lem-pur-origin-class-projective-comparison`).

Added two named holes, each in its own module with a source and complete proof in words:

- `AlgebraicGeometry.Etale.origin_boundary_counit_data`
  (`lem-pur-origin-boundary-counit-data`).
- `AlgebraicGeometry.Etale.origin_projective_normalization`
  (`lem-pur-origin-projective-normalization`).

This is a decomposition: one original hole closed, two lower holes added, net minus one.
The parent contains zero holes. The generic assembly helper is fully proved.
There are no holes in definitions or private declarations.

## No longer needed

Removed the parent's unused proof imports:
`WeilConjectures.SixFunctors.OpenClosed.Exact`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageComposition`,
`WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget`, and
`Sheaf.AlgebraicGeometry.GeometricPointCohomology`.
Their mathematical ingredients remain available in the lower steps and their dependencies.

The direct parent proof dependencies are now the two new steps. The old Cartier, twist,
compact-source, divisor and compactification nodes remain needed by their statements or
proof plans. The specialized boundary step plans to use finite base change, finite-open
comparison and Ext counit naturality directly, so the generic
`lem-pur-closed-support-open-counit` is not required by this route.
Removed the obsolete direct-parent tool approvals for
`def-weil-exact-derived-adjunction`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-etale-module-cohomology-forget`,
`lem-weil-pbc-geometric-point-cohomology`,
`lem-weil-pbc-closed-immersion-finite`, and
`lemma-weil-pbc-finite-direct-image-exact`. Their uses belong to the geometric lower steps.

No module is withdrawn and no whole-library pruning is claimed. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The retained packet did not change the assigned module, left its original hole, and its
proposed auxiliary definition repair exceeded the compiler limit. That packet is replaced
by the actual reduction above. Concrete derived-category instance conversion was the
performance problem: factoring the normalization equations into a generic categorical
predicate made the reduction compile without altering any existing arrow or target.

The existing generic counit and compact-source statements do not identify every concrete
representative in this record in one application. The two lower steps record the remaining
Cartier, exact-Ext, divisor and section-augmentation identifications explicitly. Their
natural-language proofs specify those identifications. Edge cases N=1 and the zero
coefficient ring require no nonzero generator choice; both assertions remain valid.
Blueprint searches for Kummer and normalization found no duplicate of either specialized
statement. Mathlib searches of all three required kinds are recorded in the new nodes.

## New nodes

`lem-pur-origin-boundary-counit-data`, in the new module
`Sheaf.AlgebraicGeometry.OriginBoundaryCounitData`, states only the normalized boundary
pair and actual counit compatibility. Its proof plan uses existing Cartier-boundary,
pullback, finite-twist, finite-base-change and finite-open-comparison declarations.

`lem-pur-origin-projective-normalization`, in the new module
`Sheaf.AlgebraicGeometry.OriginProjectiveNormalization`, states the positive divisor/Chern
and compact-point section normalization for any fixed normalized boundary pair. Its proof
plan uses existing Chern-realization, coefficient-forgetting, compact-source declarations and the direct Cartier-frame calculation. Neither new statement is the original theorem under another
name: the actual final compact-image identity is derived in the parent.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
