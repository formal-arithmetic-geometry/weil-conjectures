/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeLimitCore
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.Strict.StrictRoosShiftLocalization
import WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenScalarLimitCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.CompletedOpenAdjunction.CbcOpenAdjunctionBase
import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison

/-! The two independent hard components of completed open exchange.
(blueprint: lem-cbc-completed-extension-zero-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X}
variable (sq : OpenImmersionSquare gU j' j g)

/-- The Koszul/quotient comparison identifies the two specified completion units. -/
private theorem cbcComplete_iff_tower (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) : cbcCompleteProperty d T r a ha K ↔ d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change intrinsicCompletionUnit T d r a ha K _ _ ≫ c.hom = d.completionUnit T K at hc
  change IsIso (intrinsicCompletionUnit T d r a ha K _ _) ↔ IsIso (d.completionUnit T K)
  rw [← hc]
  exact (isIso_comp_right_iff _ c.hom).symm

/-- Completeness is invariant under an isomorphism, by naturality of the quotient unit. -/
private theorem cbcTowerComplete_iso {T : Scheme.{t}} {K L : d.derived T}
    (e : K ≅ L) (hK : d.TowerComplete T K) : d.TowerComplete T L := by
  let η : 𝟭 (d.derived T) ⟶ completedReductionTower T d ⋙
      completedRlim T (d.completedRing T) :=
    (d.constantRlimAdjunction T).unit ≫
      Functor.whiskerRight (completedReductionAugmentation d T)
        (completedRlim T (d.completedRing T))
  change IsIso (η.app K) at hK
  change IsIso (η.app L)
  exact (η.isIso_app_iff_of_iso e).mp hK

/-- The published reduction theorem makes completed pullback intrinsically complete. -/
private theorem cbcPullback_complete {V T : Scheme.{t}} (f : V ⟶ T)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    cbcCompleteProperty d V r a ha ((cbcCompletedPullback d f).obj K) := by
  exact (completedPullback_reduction f d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) hK).1
    (DerivedCategory.Q.objPreimage _) (DerivedCategory.Q.objObjPreimageIso _)

/-- All three endpoints of the completed open exchange are intrinsically complete.
Source: Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-route-completed-extension-zero-comparison-complete).
Proof: extension by zero preserves the Koszul completion unit; completed pullback is
the intrinsic completion reflector; apply the same argument to the base-changed open.
-/
theorem completedExtensionZeroComparison_complete [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
      cbcCompleteProperty d X r a ha
          ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
        cbcCompleteProperty d X' r a ha
          ((cbcCompletedPullback d g).obj
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
        cbcCompleteProperty d X' r a ha
          ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
            ((cbcCompletedPullback d gU).obj K.obj)) := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  have hsq : IsPullback gU j' j g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let : QuasiCompact j' := MorphismProperty.of_isPullback (P := @QuasiCompact)
    hsq inferInstance
  intro K
  have hJK := cbcShriek_complete d j r a ha K.obj K.property
  exact ⟨hJK, cbcPullback_complete d g r a ha _ hJK,
    cbcShriek_complete d j' r a ha _ (cbcPullback_complete d gU r a ha K.obj K.property)⟩

end AlgebraicGeometry.Scheme
