/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-! # Factorisation form of the inverse-pullback exchange square

Source: the source-structure calculation in `thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-factors).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.ProEtale

private lemma factor_triangle (A : Type v) [Category.{u + 1} A]
    {Z P : Scheme.{u}} (p : Z ⟶ P) (a : Z ⟶ Z) (b : P ⟶ P) (c : Z ⟶ P)
    (h : p ≫ b = c) (h' : a ≫ p = c) (e : p ≫ b = a ≫ p)
    (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarFactor A h).inv.app M ≫ (lowerStarFactor A e).hom.app M ≫
      (lowerStarFactor A (rfl : a ≫ p = a ≫ p)).inv.app M =
        (lowerStarFactor A h').inv.app M := by
  ext V : 3
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback,
    MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]

section CarrierCoherence

attribute [local irreducible] upperStar lowerStar
  upperStarIsoLowerStarInv upperStarComp lowerStarComp
  upperStarFactor lowerStarFactor upperStarCongr

/-- The inverse-pullback comparison commutes with an exchange written using a common
factorisation of the two scheme composites.

Source: the source-structure comparison in the first paragraph of blueprint
`thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-factors).

Proof: apply the existing comparison composition law to `(b,j)` and `(j,a)`,
using the same isomorphism E. Both routes begin with its canonical comparison.
The lower-star factors agree by functoriality of restriction maps: on sections,
combine the three restrictions and check the underlying canonical maps of
iterated pullbacks with pullback.hom_ext. Substituting this factor triangle
identifies the two routes. -/
theorem upperStarIsoLowerStarInv_exchange_factor (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (j : Q ≅ P) (a : P ≅ P) (b : Q ≅ Q) (E : Q ≅ P)
    (hc : b.hom ≫ j.hom = j.hom ≫ a.hom)
    (hi : j.inv ≫ b.inv = a.inv ≫ j.inv)
    (hE : b.hom ≫ j.hom = E.hom) (hEi : j.inv ≫ b.inv = E.inv)
    (M : Sheaf (Scheme.ProEt.topology P) A) :
    (upperStarFactor A hE).hom.app M ≫
      (b.hom)^*[A].map ((upperStarIsoLowerStarInv A j).hom.app M) ≫
      (upperStarIsoLowerStarInv A b).hom.app ((j.inv)_*[A].obj M) ≫
      (lowerStarFactor A hi).hom.app M ≫
      (lowerStarFactor A (rfl : a.inv ≫ j.inv = a.inv ≫ j.inv)).inv.app M =
    (upperStarFactor A (hc.symm.trans hE)).hom.app M ≫
      (j.hom)^*[A].map ((upperStarIsoLowerStarInv A a).hom.app M) ≫
      (upperStarIsoLowerStarInv A j).hom.app ((a.inv)_*[A].obj M) := by
  have L := upperStarIsoLowerStarInv_hom_app_trans A b j E hE hEi M
  have R := upperStarIsoLowerStarInv_hom_app_trans A j a E
    (hc.symm.trans hE) (hi.symm.trans hEi) M
  rw [← reassoc_of% L]
  rw [factor_triangle A j.inv a.inv b.inv E.inv
    hEi (hi.symm.trans hEi) hi M]
  exact R

end CarrierCoherence
end AlgebraicGeometry.ProEtale
