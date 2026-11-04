/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerProEtaleNaturality

/-! # Naturality of the coordinate Kummer class under the punctured base change

Clause (4) of the relative Kummer computation, first half: the derived pullback of the
coordinate class along the punctured base-change arrow is the coordinate class.
Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Pullback along the punctured base change arrow preserves the coordinate unit. -/
lemma units_map_puncturedMap_coordinateUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Units.map (puncturedMap f).appTop.hom (coordinateUnit Y) = coordinateUnit X := by
  have hs : puncturedMap f ≫ openImmersion Y =
      openImmersion X ≫ AffineSpace.map (ULift.{u} (Fin 1)) f :=
    (Classical.choose_spec (existsUnique_puncturedMap f)).1
  apply Units.ext
  change (puncturedMap f).appTop ((openImmersion Y).appTop (coordinate Y)) =
    (openImmersion X).appTop (coordinate X)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  dsimp only [coordinate, Line]
  rw [AffineSpace.map_appTop_coord]

-- keeps the elaborator from unfolding the shift structure when matching objects
attribute [local irreducible] ProEtale.commShiftLeftDerivedUpperStar in
/-- The coordinate Kummer class is compatible with the punctured base change: this is the
first clause of `KummerBaseChangeConclusions`. -/
theorem coordinateKummer_baseChange (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {B' B : Scheme.{u}} (g : B' ⟶ B)
    (a : B ⟶ Spec (CommRingCat.of P.field.k)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h B a).hom ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
          (P.derivedSheaf h (Punctured B) true) ≫
      (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
    P.derivedCoefficientPullback h (puncturedMap g) false ≫
      (P.coordinateKummer h B' (g ≫ a)).hom := by
  have := P.leftDerived_map_kummer_hom h (puncturedMap g)
    (P.exponent_isUnit _ (puncturedProjection B ≫ a))
    (P.exponent_isUnit _ (puncturedProjection B' ≫ g ≫ a)) (coordinateUnit B)
  rw [units_map_puncturedMap_coordinateUnit] at this
  unfold coordinateKummer
  exact this

end WeilConjectures.PurityFiniteSetting
