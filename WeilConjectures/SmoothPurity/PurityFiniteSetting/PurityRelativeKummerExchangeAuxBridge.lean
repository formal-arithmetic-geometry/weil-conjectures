/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerExchangeAuxKummer

/-! # Derived-category naturality of the coordinate Kummer class

Source: blueprint latest, relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-exchange-from-conclusions).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate Kummer class is natural for derived pullback along `puncturedMap g`,
through the derived coefficient pullbacks and the shift isomorphism.
Source: blueprint relative Kummer proof, Step 3.
Proof: apply `leftDerivedUpperStar_map_hom_of_ext_comp_eq` to
`coordinate_pro_kummer_pullback`. -/
theorem coordinateKummer_leftDerivedUpperStar_naturality (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.derivedSheaf h (Punctured Y) true) ≫
    (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
      P.derivedCoefficientPullback h (puncturedMap g) false ≫
        (P.coordinateKummer h Y' (g ≫ a)).hom := by
  rw [derivedCoefficientPullback_true_eq, derivedCoefficientPullback_false_eq]
  have key := ProEtale.leftDerivedUpperStar_map_hom_of_ext_comp_eq _ _ _ _ _ _
    (coordinate_pro_kummer_pullback P h g a)
  have e : (SymmetricCategory.toBraidedCategory :
      BraidedCategory (ModuleCat.{u + 1} P.Coefficient)) =
      ModuleCat.MonoidalCategory.instBraidedCategory := rfl
  rw [e] at key
  set_option maxRecDepth 100000 in
  exact key

end WeilConjectures.PurityFiniteSetting
