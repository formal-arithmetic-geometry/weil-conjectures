## What changed

Proved `AlgebraicGeometry.Scheme.cbcDatumCompletedTransport_unit`.
The proof identifies the normalized constant-tower square by its ordinary and
strict-tower counits, identifies the constant/Rlim adjunction units by their
factorization on complexes, and transports the quotient augmentation by naturality.
It applies to every ambient input of the original statement.

The public definition `CategoryTheory.Functor.ExactDerivedCounitNormalization`
names the existing normalization formula. The two transport existence theorems use
this shared condition, which unfolds to their original statements. This avoids
repeated kernel comparison of expanded choice predicates. The definition and
statement refactoring is recorded in
`coord/changes/completed-open-counit-normalization.md`. All six existing public
construction bodies remain verbatim.

The two universal-left-derived instances are projected directly from the existing
ordinary and strict-tower pullback constructors. This removes the proof import
`Sheaf.Paper.AdicPullbackPresentationTransport`. The generic derived-unit proof uses
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`; it was
already in the original transitive import closure. Pointwise exactness uses the proof
import `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`.

The item compiled through `lcompile.py` in 36.0 seconds, and again in 38.6 seconds
during the compatibility batch. All 19 consumer modules compiled. A separate
probe restated both existence theorems with their original formulas and proved
each by applying the refactored theorem; that probe compiled in 20.4 seconds.
All 21 files in the batch passed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.cbcDatumCompletedTransport_unit`.
One of one existing holes proved; zero holes added; zero holes remain in the item.
Zero statements split off.

## No longer needed

Removed the proof import `Sheaf.Paper.AdicPullbackPresentationTransport` and the
node dependency `lem-cbc-adic-pullback-presentation-transport` from Step 5. Its two
universality instances follow directly from the constructors already imported.
The completed exchange still follows the finite-exchange and derived-limit route.

Relative to the original item, the following 24 project modules leave this
module's transitive import closure. The scope of this pruning is this item's
proof dependencies.

| module | associated nodes |
| --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso | def-sfb-scalar-extension-pure-tensor-section, lem-weil-sheaf-scalar-extension-ring-iso |
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData | def-weil-pbc-successive-derived-quotient-data |
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization | lem-sfb-successive-derived-quotient-normalization, def-pbc-successive-derived-scalar-normalization-data |
| Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction | def-pe-proetale-object-restriction-comparison-data, lem-sfb-proetale-object-inverse-image-restriction |
| Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport | No direct Lean attachment |
| Sheaf.CategoryTheory.CochainCoefficientUniverseTransport | def-pur-cochain-coefficient-universe-transport |
| Sheaf.CategoryTheory.ConstantLeftModuleInverseImage | lem-pe-constant-left-module-inverse-image |
| Sheaf.CategoryTheory.ConstantLeftModuleInverseImageCoherence | lem-pe-constant-left-module-inverse-image-coherence |
| Sheaf.CategoryTheory.ConstantLeftModuleTransport | lem-pe-constant-left-module-transport, def-pur-constant-module-inverse-image-lift |
| Sheaf.Paper.AdicPullbackPresentationTransport | lem-cbc-adic-pullback-presentation-transport |
| Sheaf.Paper.CommonQuotientTowerPresentation | def-weil-pbc-common-quotient-tower-presentation |
| Sheaf.Paper.DerivedFiniteQuotientCoherence | lem-cbc-derived-finite-quotient-coherence |
| Sheaf.Paper.FlatCommonQuotientReductionTower | lem-weil-pbc-flat-common-quotient-reduction-tower |
| Sheaf.Paper.OpenImmersionTensorPiece | lemma-weil-pbc-projection-formula-open-piece-existence, lemma-weil-pbc-projection-formula-open-piece, lemma-weil-pbc-projection-formula-open-piece-projection-existence |
| Sheaf.Paper.OrdinaryCommonQuotientTower | lem-weil-pbc-ordinary-common-quotient-tower |
| Sheaf.Paper.ProjectionCompactification | def-weil-pbc-projection-compactification |
| Sheaf.Paper.StrictPerfectPackageOnSite | No direct Lean attachment |
| Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations | lem-pur-cochain-comparison-monoidal-equations |
| Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence | lem-pur-cochain-pullback-tensor-coherence |
| Sheaf.SecSmoothPurity.ModuleTensorCoefficientEquations | lem-pur-module-tensor-coefficient-equations |
| Sheaf.SecSmoothPurity.ModuleTensorCompositionEquation | lem-pur-module-tensor-composition-equation |
| Sheaf.SecSmoothPurity.ModuleTensorExtensionEquation | lem-pur-module-tensor-extension-equation |
| Sheaf.SecSmoothPurity.ModuleTensorMonoidalEquations | lem-pur-module-tensor-monoidal-equations |
| WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex | lem-sfb-termwise-strong-monoidal |

## Where the brief, the DAG or earlier work was wrong

Step 5 cited the larger presentation-transport module for facts already supplied
by the universal pullback constructors. The DAG now records the direct projections
and the counit-normalized constant-square argument. The unit statement needs no
correction and no additional hypothesis. The named normalization condition is a
representation change for kernel performance, with the original equations retained
by unfolding.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
