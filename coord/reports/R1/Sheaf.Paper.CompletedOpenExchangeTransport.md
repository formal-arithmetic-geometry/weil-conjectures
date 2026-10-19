## What changed

Proved the finite and completed coefficient equalities, ordinary and strict-tower module
functor equalities, and their equalities on complexes. Two proved private categorical
helpers construct the unique exact-derived comparisons with their specified complex
counits; these close both transport existence theorems. Proved the current strict unit
identity from the retained unit theorem, and proved the transported exchange unit by
cancelling the transport isomorphisms and using the old exchange unit equation.

Proved completedOpenExchangeComparison from completedExtensionZeroComparison.
Invertibility follows by composition with the transport isomorphisms. For completeness
of a transported pullback, apply completedPullback_reduction to the canonical
representative of the new object, realized as the old object through the transport.
Cancelling its realization isomorphism proves invertibility of the same completion
chain map. For the final open extension, apply the retained comparison to the
identity horizontal square of the base-changed quasi-compact open. All existing
public signatures and definitions remain unchanged.

Recovery validation on 2026-10-19: retained the earlier sandbox, compared its Lean
and node changes with current shared sources, and compiled the complete item with
lcompile.py successfully (40.3 seconds, exit code 0). The item contains exactly one
remaining sorry; this delivery adds no modules, no declarations with sorry, and no
new nodes. The required dry run and delivery perform the delivery checks.

## Proved and sorry left

Closed 11 of the 12 original holes:

- cbcDatumFiniteCoefficient_eq
- cbcDatumCoefficient_eq
- cbcDatumModulePull_eq
- cbcDatumTowerModulePull_eq
- cbcDatumModulePullComplex_eq
- cbcDatumTowerPullComplex_eq
- cbcDatumOrdinaryTransport_exists
- cbcDatumTowerTransport_exists
- cbcDatumActualStrictTransport_unit
- cbcDatumCompletedExchange_unit
- completedOpenExchangeComparison

One original sorry remains: AlgebraicGeometry.Scheme.cbcDatumCompletedTransport_unit
(node lem-cbc-completed-extension-zero-comparison). It still needs identification of
the counit-normalized constant-tower comparison with the datum presentation's
termwise exact comparison, followed by naturality of the constant/Rlim unit and
strict quotient augmentation. Its existing docstring gives this argument. No holes
were added and none were split off. The imported retained comparison and reduction
statements may themselves contain sorry; they remain independent obligations.

## No longer needed

Removed the following direct proof imports from this transport module:

- Mathlib.Algebra.Category.Grp.AB
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
- Mathlib.Algebra.Category.Ring.Limits
- Mathlib.Algebra.Homology.BifunctorShift
- Mathlib.Algebra.Homology.DerivedCategory.Basic
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.HomologicalComplexLimits
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective
- Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
- Mathlib.CategoryTheory.Abelian.FunctorCategory
- Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
- Mathlib.CategoryTheory.Adjunction.Limits
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.RoosComplex
- Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
- Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
- Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.LocalizedModuleExactIndependent
- Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
- Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf
- Sheaf.CategoryTheory.SiteMorphismComposition
- Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
- Sheaf.Paper.CompletedRlimFunctor
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.ExactFunctorDerivedLimit
- Sheaf.Paper.ExactProductFunctorStrictLimit
- Sheaf.Paper.PbcQbarCompletedPullback
- WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
- WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

The retained public dependency CompletedExtensionZeroComparison still needs the
underlying extension, tensor, product, finite-exchange and limit argument. Therefore
this delivery does not claim these DAG nodes or modules are globally unnecessary.
The unit has no realized steps, and the existing sheaf-theoretic comparison remains
used. Public imports are retained to preserve the importer-visible interface.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The long sheaf-theoretic proof already belongs to
the retained CompletedExtensionZeroComparison interface. Repeating it in the
transport module is unnecessary. The derived comparisons follow from uniqueness of
a universal left-derived pair and exactness, without constructing another K-flat
resolution. Completeness of transported objects can be checked on their own
representatives, avoiding any additional isomorphism-invariance lemma.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
