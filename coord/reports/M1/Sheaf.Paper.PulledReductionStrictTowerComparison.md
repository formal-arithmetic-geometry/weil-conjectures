## What changed

The original theorem statement stays unchanged. Its concrete functors and normalization
definitions move verbatim to `Sheaf.Paper.PulledReductionComparisonData`, publicly
imported by the original module. The original theorem combines the strict augmented
model comparison with the restriction-of-limits normalization, using naturality of
projections and adjunction units. The final finite-unit equation is proved directly
from naturality of the derived projection along the quotient augmentation.

`Sheaf.Paper.RestrictionLimitProjectionUnit` separates the normalization of the fixed
lambda at every derived projection and on constant-unit maps. Its proof uses the
actual universal derived units, exact evaluation square and the adjunction mate
identity. No flatness of the completed coefficient structure map is assumed.

`Sheaf.Paper.PulledReductionStrictModelDescent` isolates the augmented K-flat-model
construction (steps 1–6), including the original scalar-insertion and cochain-counit
normalizations. The full model argument and its remaining obligation are explicit.

`Sheaf.Paper.CompletedTowerPullback` also receives supporting proofs. Its coefficient
map is identified with the existing integral-ring comparison using every quotient
projection. Thus its ordinary and levelwise functors are exact, and their canonical
exact derived functors supply the required universal pairs and K-flat counit
computations. The ordinary quotient unit comes from the normalized tensor
adjunctions; its transition squares preserve one. Its derived unit is the universal
left-derived lift, with uniqueness checked on K-flat representatives. Constant-tower
pullback agrees strictly with pullback followed by constant towers, degree by degree.
Only proof imports and proved private helpers are added to this supporting module.
The localization calculation and the K-flat representative existence argument use
proved private helpers over general abelian categories and sheaf rings. This keeps
concrete coefficient-limit constructions out of their elaboration. The specialization
retains the original raw-counit equation.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Scheme.PulledReduction.strictTowerComparison` is closed by a
complete assembly proof. One new obligation remains:
`AlgebraicGeometry.Scheme.PulledReduction.strictModelComparison`
(node `lem-weil-pbc-pulled-reduction-strict-model-descent`). This part is a decomposition:
one upper hole is closed and one strictly smaller model obligation is added.
The independent
`AlgebraicGeometry.Scheme.PulledReduction.restrictionLimitNormalization`
is proved, with no internal holes.

The supporting unclaimed module `Sheaf.Paper.CompletedTowerPullback` retains all its
public declarations and definitions. Nine existing holes are closed, in namespace
`AlgebraicGeometry.Scheme`:

- `completedFiniteCoefficientMap_isIso`
- `completedCoefficientComponent_naturality`
- `completedModulePullback_additive`
- `completedTowerModulePullback_additive`
- `completedTowerPullback_exists`
- `completedOrdinaryPullback_exists`
- `completedReductionModuleUnit_exists`
- `completedReductionTowerUnit_exists`
- `completedPullbackConstantComplex_eq`

Its three untouched holes are `completedPullbackConstantIso_exists`,
`completedPullback_reductionEvaluation` and `completedPullback_isCompletion`, all
attached to `def-weil-pbc-completed-pullback`. They are not added by this delivery.
Across the two existing modules, ten of thirteen original holes are closed and one
new hole is added: four holes remain, for a net reduction of nine. No definition
contains a hole; the new helpers are private and proved. No arbitrary data witness
is introduced.

The original theorem signature and all moved construction bodies have been compared
with the current repository and are unchanged. The final five-module `lcompile.py --all` check compiled cleanly: the supporting
module in 30.1 seconds, the data module in 9.8 seconds, strict-model statement in
11.1 seconds, restriction normalization in 48.2 seconds and original comparison in
37.1 seconds. A direct abstract-theorem application avoids unpacking and repacking
the derived-unit witness; this reduced the supporting module from its earlier
47.0-second check after a delivery compile reached the 60-second limit. The remaining strict-model obligation is explicitly a decomposition,
not a claim that the original assertion has no transitive proof holes.

## No longer needed

The following direct proof imports leave the original module:

- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
- `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`

The supporting `CompletedTowerPullback` module also drops its proof-only imports of
`Sheaf.Algebra.Homology.DiagramKFlatReplacements`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
`Sheaf.Algebra.Homology.KFlat` and
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
Its new proofs use exact-functor localization, the existing normalized tensor
adjunctions, and the K-flat resolution API directly.

Reviewer correction (FIX): `Sheaf.Paper.FlatCommonQuotientReductionTower` is not a
module of a node in `realized` of dag/units/sk-thm-properbasechange.json, and the
original module's proof no longer uses it; the import is removed from
`Sheaf.Paper.PulledReductionStrictTowerComparison`. Its node stays in the proof_deps of
`lem-weil-pbc-pulled-reduction-strict-model-descent`, the remaining obligation.
The five plain imports copied into `Sheaf.Paper.PulledReductionComparisonData` from the old
module (`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
`Sheaf.Paper.PbcQbarCompletedPullback`, `Sheaf.Paper.RingedTopoiTensorSections`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`, `Mathlib.CategoryTheory.Abelian.FunctorCategory`)
are not needed by its definitions and are removed as well.
The K-flat, inverse-image and tensor dependencies remain in the proof plan of the
strict-model lemma. They are not claimed as mathematically pruned. No source-library
declaration, DAG parent or unit step is withdrawn. The original public imports are
preserved, with the new data module added. The shared data module keeps only its
public construction imports. No module is claimed globally pruned. The current downstream consumers are
`Sheaf.Paper.PulledReductionNormalizationComparison` (held by E9) and
`Sheaf.Paper.IntegralPullbackStrictRoosNormalization` (unclaimed); neither needs
an adaptation because all moved declarations remain publicly available.

## Where the brief, the DAG or earlier work was wrong

The original nine-step statement has been checked on the edge cases:
zero objects, identity morphisms, zero or unit adic ideal and unbounded inputs. Its
strict-model construction and its independent right-derived-limit normalization
require different localization computations. The retained strict-model result still needs the
augmented diagram resolution, its pulled quasi-isomorphism, and descent retaining the actual
scalar-insertion unit. Existing exact-pullback transports alone do not supply those
normalizations. These two parts are now separated explicitly;
the original target-facing statement and the unit route are retained.

This resumed attempt inherited the four-module packet after the dispatcher's recorded
SIGTERM failure (retry 1 of 5). The fresh delivery reference started at
2026-10-21 18:32 UTC. Its first delivery check rejected a new split after 30 minutes
against a 72-minute minimum. The packet was retained, the budget metadata was not
edited, and work continued on the existing pullback and unit proof obligations.

The delivery preflight identified missing LeanSearch records in the inherited new
nodes and a recorded abbreviation body where only its signature was expected.
Real LeanSearch queries have now been run and recorded for each new node; the
abbreviation record follows the signature extractor. (The import retained here as
"unit-route" was not one; see `## No longer needed`.)

## New nodes

`def-weil-pbc-pulled-reduction-comparison-data` attaches the unchanged concrete
definitions to their shared module. Its construction uses the actual prescribed
model-site pullback unit and does not choose an arbitrary adjunction.

`lem-weil-pbc-pulled-reduction-strict-model-descent` is the augmented model part of
the source argument, with no derived inverse-limit assertion. Its docstring retains
the six construction and descent steps, including the augmented indexing category.

`lem-weil-pbc-restriction-limit-projection-unit` records the projection and
constant-unit normalization of the existing lambda on arbitrary derived towers.

Change record: `coord/changes/pulled-reduction-comparison-data.md`.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
