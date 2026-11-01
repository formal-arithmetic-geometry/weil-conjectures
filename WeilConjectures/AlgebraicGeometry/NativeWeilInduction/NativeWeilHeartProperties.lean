/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilInductionComparisonData
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilFreeCoproduct
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts

/-! # Native Weil heart and free coproduct properties -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry.NativeWeilInduction

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

omit [Fact (ringChar k₀ ≠ l)] in
/-- Structural and coproduct properties of the native Weil heart.
Source: comparison proof steps 1--2, Stacks Tags 079P and 08BJ.
(blueprint: lem-sf-native-weil-heart-properties)

Proof: the native module category is Grothendieck. Apply the fixed-pair and
free-derived-resolution theorems to its exact Frobenius autoequivalence. These give
exactness, conservativity, preservation of K-injectives, and derived coproduct
preservation for forgetting. Exact Frobenius pullback preserves bounded constructible
complexes; its inverse image of the constructible localizing hull is localizing and
contains the constructible generators. Finally localize the termwise free coproduct
cocone. Exact localization preserves the coproduct and its structure isomorphism;
the localized free adjunction unit is its zeroth coprojection. The integer structure
recurrence identifies every other coprojection with `inclusion`, including negative
indices. Thus the displayed cofan is colimiting. -/
theorem nativeWeil_heart_properties
    (T : Scheme.{u}) [T.Over (Spec (.of k₀))] : HeartProperties k₀ l T := by
  let C := ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber
  let P := WeilSheaf.frobeniusPullback k₀ l T
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1} C ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1} C ℤ
  have hd := IsoAlgebra.freeWeil_derived_properties P
  have hcons : ∀ A, ProEtale.DerivedCategory.boundedAdicConstructible l
      (T ↘ Spec (.of k₀)).geometricFiber A →
      ProEtale.DerivedCategory.boundedAdicConstructible l
        (T ↘ Spec (.of k₀)).geometricFiber ((frobenius k₀ l T).obj A) := by
    intro A hA
    let e := ProEtale.adicUpperStarIsoLowerStarInv l
      (T ↘ Spec (.of k₀)).geometricGaloisFrobenius
    have he := (Functor.mapDerivedCategoryNatIso e).app A
    have hp := ProEtale.DerivedCategory.boundedAdicConstructible_mapDerivedCategory_upperStar
      (T ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom hA
    exact ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_iso he hp.1,
      fun i ↦ (ProEtale.adicConstructibleSheaf l _).prop_of_iso
        ((_root_.DerivedCategory.homologyFunctor _ i).mapIso he) (hp.2 i)⟩
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hd.2.1,
    hd.2.2.2.1, inferInstance, hd.2.2.2.2, hcons, ?_,
    nativeWeil_free_coproduct k₀ l T⟩
  have (J : Type (u + 1)) : HasColimitsOfShape (Discrete J) C :=
    IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1} C J
  have (J : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete J) (frobenius k₀ l T) :=
    P.mapDerivedCategory_preservesCoproducts J
  let L := ProEtale.nativeAdicConstructibleLocalizingHull l
    (T ↘ Spec (.of k₀)).geometricFiber
  have : (L.inverseImage (frobenius k₀ l T)).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete J :=
        { colimitsOfShape_le := by
            rintro A ⟨h⟩
            exact L.prop_of_isColimit
              (isColimitOfPreserves (frobenius k₀ l T) h.isColimit) h.prop_diag_obj } }
  have hl : (ProEtale.DerivedCategory.boundedAdicConstructible l
      (T ↘ Spec (.of k₀)).geometricFiber).localizingClosure ≤
        L.inverseImage (frobenius k₀ l T) :=
    ObjectProperty.localizingClosure_le
      (fun A hA ↦ ObjectProperty.le_localizingClosure _ _ (hcons A hA))
  exact hl

end AlgebraicGeometry.NativeWeilInduction
