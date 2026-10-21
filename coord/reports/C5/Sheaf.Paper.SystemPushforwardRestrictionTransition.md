## What changed

Implemented the four clauses of
`WeilConjectures.SemilinearSections.Geometry.systemPushforwardRestrictionTransition`
using iterated mates, localization of the ordinary horizontal transition square,
the evaluated counit equations, and the normalized right-derived unit.
The generic localization, transition, and mate calculations are proved private helpers.
In particular, the transition square is localized with abstract exact functors before
specializing to pro-etale module categories, avoiding expensive concrete unfolding.
The already-proved `exactSquare_fac` normalization is reused through
`import all Sheaf.CategoryTheory.DerivedExactSquareComposition`.
The existing proved `derived_mate_factors` calculation is reused through a private
`import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.

Repaired `WeilConjectures.SemilinearSections.Geometry` in
`Sheaf.Paper.SemilinearGeometryDerived`: `ordinaryPullTransition` specifies the ordinary
horizontal arrows of termwise inverse image before localization. All existing fields
and all existing theorem signatures are unchanged. The change record is
`coord/changes/C5-system-horizontal-transition.md`; the definition node includes the
complete DAG citer audit. Source search found no existing Geometry constructor literal
or positional constructor application, so no consumer needs source adaptation.

## Proved and sorry left

Original hole: `WeilConjectures.SemilinearSections.Geometry.systemPushforwardRestrictionTransition`
(blueprint: `lem-pur-system-pushforward-restriction-transition`).
Closed 1 of 1 original holes: the declaration above. There are no `sorry` declarations
left in the delivered modules, and no holes are added. The server compiled both modules
together successfully: `SemilinearGeometryDerived` in 27.3 seconds and
`SystemPushforwardRestrictionTransition` in 26.0 seconds. A subsequent whitespace-only
edit removes the sole style warning; the delivery preflight checks the final text.
Split off: 0 statements. The definition repair adds
one ordinary normalization equation as a structure field, not as a proof obligation
hidden inside a definition. All private helper proofs have no `sorry`.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  the resolution equation follows from normalized mates and naturality; its
  invertibility proves the image replacement is a quasi-isomorphism.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  the supplied scalar adjunctions and their transpose equation already suffice.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  no tensor or composition comparison is rebuilt.
- The redundant direct `Mathlib.CategoryTheory.Adjunction.Mates` import: the existing
  public semilinear calculus imports it already.
- The redundant direct proof import `Sheaf.Paper.SemilinearGeometryDerived`:
  the existing public imports already provide this interface.

Corresponding proof dependencies no longer used are
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-sfb-ringed-derived-monoidal-comparisons`, and `def-weil-size-convention`.
`lem-coef-semilinear-derived-sections` remains an ambient statement dependency and
its module remains publicly imported, but its existence theorem is not used in this
proof. Obsolete entries for these nodes are removed from this item's `tool_uses`,
with the order of retained approvals preserved. The direct-import cleanup does not withdraw these modules: in particular,
`RingedToposDerivedPushforwardComposition` remains a transitive import of the existing
ring-change module. No module is withdrawn and no adopted source declaration is removed. The unit's own statements and realized route are preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan applied the extension-form transition theorem to an arbitrary supplied
`G : Geometry`. The actual `semilinearDerivedSections` theorem constructs a chosen
geometry with that property; it does not give it for every input geometry. The
interface specified component evaluation and adjunction normalizations but omitted
an explicit ordinary horizontal-transition equation. This delivery states that
ordinary construction equation, localizes it, and proves the push transition by
mates. It does not add the requested derived push-transition or resolution formula
as an assumption.

The old plan also invoked the general derived composition theorem for the replacement
normalization. The already-proved normalized-mate calculation gives the needed square
directly; invertibility of its other factors supplies the quasi-isomorphism assertion.
The ordinary coefficient mate is invertible because its underlying sheaf map is the
comparison of the two specified direct-image realizations, proved using normalized
ordinary Hom correspondences.

The changed definition is reachable from target statements, so its statement-meaning
review is reopened under AGENTS.md §4, as recorded in the change record. No target
signature changes. The definition repair is unclaimed apart from this delivery;
no forced adaptation of another group's module is included. The first preflight found
two consumers added since the initial audit (`NormalizedOperationSystemModels` and
`QuotientDiagramProjectionEvaluation`); both were read and added to the Users audit,
and the quotient-diagram node was added to the complete DAG citer list.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
