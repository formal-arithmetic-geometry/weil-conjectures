/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationUpperStar
public import WeilConjectures.WeilSheaf.Native.Projection.DerivedMateComposite
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunctionMate
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.Tactic.ExactModProofs

/-! # The proper realization square through the adic model -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The comparison of direct images induced by the pullback comparison of the two models. -/
def projectionAdicCondensedPushIso :
    (adicLowerStar l g) ⋙ (adicSheafEquivCondensedMod l Y).functor ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g := by
  let a := adicUpperStarLowerStarAdjunction l g
  let b := CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g
  have : IsIso (mateEquiv a b (adicUpperStarCompCondensedModIso l g).inv).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Adjunction.isIso_mateEquiv_app_of_isIso a b
      (adicUpperStarCompCondensedModIso l g).symm
      (adicSheafEquivCondensedMod l _).toAdjunction
      (adicSheafEquivCondensedMod l _).toAdjunction M
  exact asIso (mateEquiv a b (adicUpperStarCompCondensedModIso l g).inv).natTrans

/-- The corresponding derived direct-image comparison. -/
def projectionAdicCondensedDerivedPushIso :
    (adicLowerStar l g).rightDerivedFunctor ⋙ (adicSheafDerivedEquivCondensedMod l Y).functor ≅
      (adicSheafDerivedEquivCondensedMod l X).functor ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor := by
  have := Equivalence.preservesKInjectiveComplexes_functor (adicSheafEquivCondensedMod l X)
  exact Functor.rightDerivedFunctorCommIso (projectionAdicCondensedPushIso l g)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

local notation "gb" => Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))
local notation "Λ" => Profinite.padicAlgClRingObj l

/-- The underived realization mate factors through the adic model. -/
lemma nativeProjectionUnderivedPushMate_normalization :
    (mateEquiv (upperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.upperStarLowerStarAdjunction Λ gb)
      (condensedRealizationUpperStarIso k₀ l g).hom).natTrans =
      (Functor.isoHComp
        (IsoAlgebra.mapOfNatIsoCompForgetIso
          (adicLowerStarGeometricFiberMapCompFrobeniusIso l g
            (comp_over g (Spec (CommRingCat.of k₀))))).symm
        (projectionAdicCondensedPushIso l gb).symm).symm.hom := by
  let a := upperStarLowerStarAdjunction k₀ l g
  let b := adicUpperStarLowerStarAdjunction l gb
  let c := CondensedRing.upperStarLowerStarAdjunction Λ gb
  let α₁ := (IsoAlgebra.mapOfNatIsoCompForgetIso
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))).symm
  let α₂ := (adicUpperStarCompCondensedModIso l gb).symm
  let β₁ := IsoAlgebra.mapOfNatIsoCompForgetIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))
  let β₂ := projectionAdicCondensedPushIso l gb
  have h₁ : (mateEquiv a b α₁.hom).natTrans = β₁.hom := by
    ext K : 2
    exact IsoAlgebra.mateEquiv_mapOfNatIsoCompForgetIso_inv_app b
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l g
        (comp_over g (Spec (CommRingCat.of k₀))))
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l g
        (comp_over g (Spec (CommRingCat.of k₀))))
      (mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l g
        (comp_over g (Spec (CommRingCat.of k₀)))) K
  have h₂ : (mateEquiv b c α₂.hom).natTrans = β₂.hom := rfl
  exact mateEquiv_isoHComp_eq a b c α₁ α₂ β₁ β₂ h₁ h₂

/-- The derived realization mate is the right-derived canonical commutation square. -/
lemma nativeProjectionDerivedPushMate_normalization :
    (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ gb)
      (derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans =
      (Functor.rightDerivedFunctorCommIso
        (Functor.isoHComp
          (IsoAlgebra.mapOfNatIsoCompForgetIso
            (adicLowerStarGeometricFiberMapCompFrobeniusIso l g
              (comp_over g (Spec (CommRingCat.of k₀))))).symm
          (projectionAdicCondensedPushIso l gb).symm).symm).hom := by
  exact Adjunction.mateEquiv_derivedSquare_eq_rightDerivedFunctorCommIso
    (upperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.upperStarLowerStarAdjunction Λ gb)
    (condensedRealizationUpperStarIso k₀ l g) _
    (nativeProjectionUnderivedPushMate_normalization k₀ l g)

/-- The canonical proper pushforward comparison is the paste of the canonical adic forget
comparison and a comparison through the equivalence of geometric models. -/
lemma nativeProjectionPushMate_normalization
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ gb)
      (derivedCondensedRealizationUpperStarIso k₀ l g).hom).app M =
      (Functor.mapDerivedCategoryCompIso
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (adicSheafEquivCondensedMod l _).functor).hom.app
          ((lowerStar k₀ l g).rightDerivedFunctor.obj M) ≫
      (adicSheafDerivedEquivCondensedMod l _).functor.map
        ((IsoAlgebra.derivedForgetCommIso
          (adicLowerStarGeometricFiberMapCompFrobeniusIso l g (comp_over g (Spec (CommRingCat.of k₀))))).hom.app M) ≫
      (projectionAdicCondensedDerivedPushIso l gb).hom.app
        ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory.obj M) ≫
      (CondensedRing.lowerStar Λ gb).rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryCompIso
          (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
          (adicSheafEquivCondensedMod l _).functor).inv.app M) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := Equivalence.preservesKInjectiveComplexes_functor (adicSheafEquivCondensedMod l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  have hm := NatTrans.congr_app (nativeProjectionDerivedPushMate_normalization k₀ l g) M
  rw [Functor.rightDerivedFunctorCommIso_isoHComp_inv_app] at hm
  exact_mod_proofs hm

end AlgebraicGeometry.ProEtaleWeilSheaf
