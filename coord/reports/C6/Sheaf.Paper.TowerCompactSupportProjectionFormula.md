## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerProjection.maps_natural` and
`AlgebraicGeometry.ProEtale.SpTowerProjection.canonicalIso_natural` without changing any
existing declaration signature, definition body, public import or module layout.

The proper naturality square is the uncurried naturality square of the existing
`Adjunction.rightAdjointProjectionMap`, using the specified tensor-pullback comparison.
A proved private helper derives open-unit-transpose naturality directly from
`Operations.openTensor_mate`, naturality of the open adjunction unit, and naturality
of the inverse tensor-pullback comparison. Applying proper direct image gives the
second square of `maps_natural`.

For `canonicalIso_natural`, invert the open-map naturality square by cancellation,
and compose it with proper-map naturality and naturality of the recorded pullback
composition comparison. Expanding `projection` identifies this composite with the
actual forward map of `canonicalIso`. This argument uses ambient morphisms and
never infers equality from level evaluations.

Added the private proof import
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`. Retained all four public
imports. The proof follows the existing declaration docstrings; no new statement,
DAG node, data construction or mathematical route was introduced.

## Proved and sorry left

Closed two of the original five holes:

- `AlgebraicGeometry.ProEtale.SpTowerProjection.maps_natural`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.canonicalIso_natural`.

Three original holes remain, each attached to the existing node
`lem-sp-tower-compact-support-projection-formula` and retaining its original complete
proof docstring:

- `AlgebraicGeometry.ProEtale.SpTowerProjection.properMap_evaluation`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.openMap_evaluation`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.tower_compact_support_projection_formula`.

Added zero holes. The private helper `openTensorInv_natural` is completely proved.
This is a partial proof delivery, not a claim to have proved bounds, evaluation,
or the full projection formula.

## No longer needed

Removed these unused private proof imports from this module:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.Paper.OpenImmersionLocalizing`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.Algebra.Homology.RingedSiteTorFlatModel`.
- `Sheaf.Paper.FiniteDiscreteCondensedRing`.
- `Sheaf.Paper.FiniteDiscreteSchemeRing`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Paper.CondensedConstantConstructibility`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`.
- `Sheaf.Paper.FiniteProperBaseChange`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

The completed naturality proofs need none of these imports. Their old appearances
were imports for the unimplemented larger proof plan. No public import was removed.
No node or module is withdrawn: the unfinished bounds/evaluation/invertibility
argument still has its declared dependencies, and other consumers can still need
every module listed above. In particular
`lem-sp-tower-projection-domain-evaluation` and
`lem-sp-finite-level-projection-factors` are not claimed to be globally pruned.
The existing DAG route for the remaining holes is retained. No whole module is
claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The declared proof dependency `Sheaf.Paper.TowerProjectionDomainEvaluation` publicly
imports this item to reuse its arrows and evaluation/naturality declarations.
Consequently this item cannot directly import that dependency: the read-only check
`python3 tools/import_direction.py may Sheaf.Paper.TowerCompactSupportProjectionFormula
Sheaf.Paper.TowerProjectionDomainEvaluation` reports that it would close a cycle.
That dependency is currently held by G4. This delivery does not change its interface
or work around the import check; it closes the independent naturality holes using
the existing adjunction API. A subsequent assembly of the main theorem needs the
shared arrow definitions and evaluation API placed below both modules.

The source docstring correctly predicts the naturality argument. In fact
`openMap` is already the image of an inverse isomorphism by definition, so its
invertibility needs no finite-level argument for the naturality calculation.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
