/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.DeligneLaumon.ConstantFieldTransportComparisonFactors

/-! # Inverse-pullback comparison and commuting scheme automorphisms

Source: the source-structure calculation in `thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-square).
-/

@[expose] public section
set_option autoImplicit false
universe v u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStar lowerStar upperStarIsoLowerStarInv
  upperStarComp lowerStarComp upperStarFactor lowerStarFactor upperStarCongr

private lemma precompose_eq {C : Type v} [Category C] {A B D : C}
    (k : A ⟶ B) {f g : B ⟶ D} (h : f = g) : k ≫ f = k ≫ g :=
  congrArg (fun p ↦ k ≫ p) h

private lemma compositor_square (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (j : Q ≅ P) (a : P ≅ P) (b : Q ≅ Q)
    (hc : b.hom ≫ j.hom = j.hom ≫ a.hom)
    (M : Sheaf (Scheme.ProEt.topology P) A) :
    (upperStarComp A b.hom j.hom).hom.app M ≫
      (upperStarCompIso A hc).hom.app M =
    (upperStarCongr A hc).hom.app M ≫
      (upperStarComp A j.hom a.hom).hom.app M := by
  have h : (upperStarComp A b.hom j.hom).hom ≫
      (upperStarCompIso A hc).hom =
      (upperStarCongr A hc).hom ≫ (upperStarComp A j.hom a.hom).hom := by
    change (upperStarComp A b.hom j.hom).hom ≫
      ((upperStarComp A b.hom j.hom).inv ≫
        (upperStarCongr A hc).hom ≫ (upperStarComp A j.hom a.hom).hom) = _
    exact Iso.hom_inv_id_assoc _ _
  exact NatTrans.congr_app h M

/-- The inverse-pullback comparison intertwines commuting scheme automorphisms,
with a specified common composite isomorphism.

Source: the source-structure comparison in the first paragraph of blueprint
`thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-square).

Proof: apply the factorisation-form exchange square with E kept abstract.
The existing upperStarCompIso_eq_upperStarFactor identifies the full pullback
square with the inverse first factor followed by the second factor. Cancel
the first factor in the exchange equality. Precompose by the first compositor;
expanding upperStarCompIso cancels its inverse and gives the displayed equation.
Keeping E abstract avoids converting adjoint comparisons at an explicit composite.
This statement contains no Weil structure map or Frobenius iteration. -/
private theorem exchange_with_composite (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (j : Q ≅ P) (a : P ≅ P) (b : Q ≅ Q) (E : Q ≅ P)
    (hc : b.hom ≫ j.hom = j.hom ≫ a.hom)
    (hi : j.inv ≫ b.inv = a.inv ≫ j.inv)
    (hE : b.hom ≫ j.hom = E.hom) (hEi : j.inv ≫ b.inv = E.inv)
    (M : Sheaf (Scheme.ProEt.topology P) A) :
    (upperStarComp A b.hom j.hom).hom.app M ≫
      (b.hom)^*[A].map ((upperStarIsoLowerStarInv A j).hom.app M) ≫
      (upperStarIsoLowerStarInv A b).hom.app ((j.inv)_*[A].obj M) ≫
      (lowerStarFactor A hi).hom.app M ≫
      (lowerStarFactor A (rfl : a.inv ≫ j.inv = a.inv ≫ j.inv)).inv.app M =
    (upperStarCongr A hc).hom.app M ≫
      (upperStarComp A j.hom a.hom).hom.app M ≫
      (j.hom)^*[A].map ((upperStarIsoLowerStarInv A a).hom.app M) ≫
      (upperStarIsoLowerStarInv A j).hom.app ((a.inv)_*[A].obj M) := by
  have H := upperStarIsoLowerStarInv_exchange_factor A j a b E hc hi hE hEi M
  have W := NatTrans.congr_app (congrArg Iso.hom
    (upperStarCompIso_eq_upperStarFactor A hc hE (hc.symm.trans hE))) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at W
  have W' : (upperStarFactor A (hc.symm.trans hE)).hom.app M =
      (upperStarFactor A hE).hom.app M ≫ (upperStarCompIso A hc).hom.app M := by
    rw [W]
    simp only [Iso.hom_inv_id_app_assoc]
  conv_rhs at H => rw [W']
  simp only [Category.assoc] at H
  have K := (cancel_epi ((upperStarFactor A hE).hom.app M)).mp H
  have K' := precompose_eq ((upperStarComp A b.hom j.hom).hom.app M) K
  rw [reassoc_of% (compositor_square A j a b hc M)] at K'
  exact K'

/-- The canonical inverse-pullback comparison intertwines a commuting
square of scheme automorphisms.

Source: the source-structure calculation in `thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-square).

Proof: the private factorisation calculation keeps its common composite abstract
until after cancellation. Supply the composite isomorphism b followed by j;
its hom and inverse are exactly the two specified composites. -/
private theorem exchange_component (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (j : Q ≅ P) (a : P ≅ P) (b : Q ≅ Q)
    (hc : b.hom ≫ j.hom = j.hom ≫ a.hom)
    (hi : j.inv ≫ b.inv = a.inv ≫ j.inv)
    (M : Sheaf (Scheme.ProEt.topology P) A) :
    (upperStarComp A b.hom j.hom).hom.app M ≫
      (b.hom)^*[A].map ((upperStarIsoLowerStarInv A j).hom.app M) ≫
      (upperStarIsoLowerStarInv A b).hom.app ((j.inv)_*[A].obj M) ≫
      (lowerStarFactor A hi).hom.app M ≫
      (lowerStarFactor A (rfl : a.inv ≫ j.inv = a.inv ≫ j.inv)).inv.app M =
    (upperStarCongr A hc).hom.app M ≫
      (upperStarComp A j.hom a.hom).hom.app M ≫
      (j.hom)^*[A].map ((upperStarIsoLowerStarInv A a).hom.app M) ≫
      (upperStarIsoLowerStarInv A j).hom.app ((a.inv)_*[A].obj M) := by
  exact exchange_with_composite A j a b (b ≪≫ j) hc hi rfl rfl M

/-- The inverse-pullback comparisons give equal natural transformations around
an exchange square of scheme automorphisms.

Source: the source-structure comparison in `thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-source-constant-field-comparison-square).

Proof: extensionality reduces the identity to the component square, obtained
by the common-factorisation argument above. Keeping this identity at the
natural-transformation level permits specialization of the isomorphism before
evaluating its components. -/
theorem upperStarIsoLowerStarInv_exchange (A : Type v) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {P Q : Scheme.{u}}
    (j : Q ≅ P) (a : P ≅ P) (b : Q ≅ Q)
    (hc : b.hom ≫ j.hom = j.hom ≫ a.hom)
    (hi : j.inv ≫ b.inv = a.inv ≫ j.inv) :
    (upperStarComp A b.hom j.hom).hom ≫
      Functor.whiskerRight (upperStarIsoLowerStarInv A j).hom (b.hom)^*[A] ≫
      Functor.whiskerLeft (j.inv)_*[A] (upperStarIsoLowerStarInv A b).hom ≫
      (lowerStarFactor A hi).hom ≫
      (lowerStarFactor A (rfl : a.inv ≫ j.inv = a.inv ≫ j.inv)).inv =
    (upperStarCongr A hc).hom ≫ (upperStarComp A j.hom a.hom).hom ≫
      Functor.whiskerRight (upperStarIsoLowerStarInv A a).hom (j.hom)^*[A] ≫
      Functor.whiskerLeft (a.inv)_*[A] (upperStarIsoLowerStarInv A j).hom := by
  apply NatTrans.ext
  funext M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    exchange_component A j a b hc hi M

end AlgebraicGeometry.ProEtale
