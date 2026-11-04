/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerExchangeAux

/-! # The punctured exchange from Kummer naturality

Source: blueprint latest, relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The punctured exchange is invertible, granted the naturality of the coordinate class
(clause (4) first part) and the compatibility of the constant coefficient pullbacks with the
square. Source: blueprint relative Kummer proof, Step 3, punctured square
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
Proof: the degree-one homology of the exchange is degree zero of its shift. The shifted
exchange carries the derived pullback of the generator over `B` to the generator over `B'`, up
to coefficient isomorphisms; both generators are invertible in degree zero. -/
theorem isIso_puncturedBaseChange_of_kummer_naturality (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k))
    (hB : P.RelativeKummerConclusions h B a)
    (hB' : P.RelativeKummerConclusions h B' (g ≫ a))
    (hκ : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h B a).hom ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
          (P.derivedSheaf h (Punctured B) true) ≫
      (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
        P.derivedCoefficientPullback h (puncturedMap g) false ≫
          (P.coordinateKummer h B' (g ≫ a)).hom)
    (hρ : (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} P.Coefficient)
        (puncturedSquare g)).hom.app (P.derivedSheaf h B false) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor.map
          (P.derivedCoefficientPullback h (puncturedProjection B) false) ≫
      P.derivedCoefficientPullback h (puncturedMap g) false =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection B')).leftDerivedFunctor.map
            (P.derivedCoefficientPullback h g false) ≫
        P.derivedCoefficientPullback h (puncturedProjection B') false) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
      (puncturedSquare g)).app (P.derivedSheaf h (Punctured B) true)) := by
  have hX := P.exponent_isUnit (Punctured B) (puncturedProjection B ≫ a)
  have hY := P.exponent_isUnit B a
  have hcg := P.isIso_derivedCoefficientPullback h g false hY
  have hcK := P.isIso_derivedCoefficientPullback h (puncturedMap g) true hX
  have h₁ := isIso_homology_leftDerivedUpperStar_map (ModuleCat.{u + 1} P.Coefficient) g _ 0
    (P.isIso_homology_zero_kummerAdjoint h B a hB.2.2.2.2.1)
  have h₂ := P.isIso_homology_zero_kummerAdjoint h B' (g ≫ a) hB'.2.2.2.2.1
  have h₃ := isIso_map_derivedBaseChangeMap_shift (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g) (C := P.derivedSheaf h B false) (C' := P.derivedSheaf h B' false)
    (CP := P.derivedSheaf h (Punctured B) false) (K := P.derivedSheaf h (Punctured B) true)
    (CP' := P.derivedSheaf h (Punctured B') false) (K' := P.derivedSheaf h (Punctured B') true)
    (P.derivedCoefficientPullback h (puncturedProjection B) false)
    (P.derivedCoefficientPullback h (puncturedProjection B') false)
    (P.derivedCoefficientPullback h (puncturedMap g) false)
    (P.derivedCoefficientPullback h (puncturedMap g) true)
    (P.derivedCoefficientPullback h g false) (P.coordinateKummer h B a).hom
    (P.coordinateKummer h B' (g ≫ a)).hom hκ hρ (DerivedCategory.homologyFunctor _ 0) h₁ h₂
  have en := ((DerivedCategory.homologyFunctor _ 0).shiftIso (1 : ℤ) 0 1
    (add_zero 1)).hom.naturality ((ProEtale.derivedBaseChangeMap
      (ModuleCat.{u + 1} P.Coefficient) (puncturedSquare g)).app
        (P.derivedSheaf h (Punctured B) true))
  have : IsIso (((DerivedCategory.homologyFunctor _ 0).shiftIso (1 : ℤ) 0 1
      (add_zero 1)).hom.app _ ≫ ((DerivedCategory.homologyFunctor _ 0).shift (1 : ℤ)).map
        ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
          (puncturedSquare g)).app (P.derivedSheaf h (Punctured B) true))) := by
    rw [← en]
    exact IsIso.comp_isIso' h₃ inferInstance
  rw [isIso_comp_left_iff, DerivedCategory.shift_homologyFunctor] at this
  exact P.isIso_puncturedBaseChange_of_isIso_homology_one h g a hB hB' this

end WeilConjectures.PurityFiniteSetting
