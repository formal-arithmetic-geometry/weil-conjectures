/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.SmoothPurity.CompletedExtensionZeroComparisonLegacy
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.CompletedOpenAdjunction.CbcOpenAdjunctionBase
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
public import WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
public import WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
public import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
public import WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
public import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.RelativeCompactSupport.RelativeCompactSupportPasting
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange

/-! # Historical completed open-exchange normalization

This is the unchanged compatibility declaration retained by the interface repository
in commit 16d47025183. It is not the current condensed-coefficient theorem. The current
normalization is `AlgebraicGeometry.ProEtale.CondensedRing.completedOpenExchangeLimitCore`
in `Sheaf.Paper.CompletedOpenExchangeLimitCore`, which does not import this archive.
The two consumers of this declaration have their own route-switch repairs pending.
No proof is replaced, no new obligation is introduced, and the existing hole is retained.
Source: historical Stacks 03DI / 091N normalization, preserved verbatim below.
(blueprint: lem-cbc-completed-open-exchange-limit-core).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

/-! The former completed-coefficient statement, kept under the name `_legacy` (interface
repository, 2026-11-03) because its two consumers `CompletedOpenExchangeLimitNormalization`
and `CompletedExtensionZeroComparisonComponents` still use it until their route-switch repairs.
Its proof was `by sorry` before this delivery too; no hole is added. -/

namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- Strict quotient/open exchange after derived inverse limit: the canonical completed
exchange `cbcCompletedExchange`, followed by the open/limit comparison of `j'_!`, is
Rlim of the reduction comparison for `j_!` pulled back along `g` followed by the
simultaneous strict exchange.
Source: Stacks 03DI (lemma-extension-by-zero), 091N (derived-completion universal property);
blueprint: lem-cbc-completed-open-exchange-limit-normalization, finite-exchange and
final-limit paragraphs.
Proof: Represent K by a flat-term K-flat complex. The ordinary inverse exchange is its
open-unit transpose; applied at every strict quotient, with its transition maps, it is
the simultaneous strict exchange `cbcReductionStrictExchange`. The constant-diagram mate
`cbcRealizationLimitMap` commutes with the strict quotient augmentations, since its
transpose is `compConstIso`; for quasi-compact `j'` it is invertible because extension
by zero preserves countable products. Hence Rlim of the reduction exchange followed by
the inverse open/limit comparison satisfies the ordinary-to-completed unit equation
defining `cbcCompletedExchange` (`cbcCompletedExchange_exists`). Source and target are
complete, so that equation determines the map; composing with the forward open/limit
comparison gives the displayed equation.
(blueprint: lem-cbc-completed-open-exchange-limit-core). -/
theorem completedOpenExchangeLimitCore_legacy [QuasiCompact j]
    (sq : OpenImmersionSquare v j' j g) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
    (cbcCompletedExchange d sq r a ha).app K ≫
        (cbcRealizationLimitMap (cbcOpenShriek d j' inferInstance)).app
          ((completedTowerPullback v d).obj ((completedReductionTower U d).obj K.obj)) =
      (completedRlim T' (d.completedRing T')).map
        ((completedTowerPullback g d).map (cbcRealizationReduction d j K.obj).hom ≫
          (cbcReductionStrictExchange d sq).hom.app K.obj) := by
  sorry

end AlgebraicGeometry.Scheme
