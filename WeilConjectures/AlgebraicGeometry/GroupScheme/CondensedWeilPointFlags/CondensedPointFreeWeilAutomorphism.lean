/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
/-! # Free modules with a specified Weil automorphism

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-free-automorphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags
/-- Equip the actual free module with the supplied automorphism after the canonical
Frobenius pullback comparison. This is a concrete fixed pair.
Source: latest blueprint, dimension-zero Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-free-automorphism). -/
def freeWeilObject (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (t : free D l n ≅ free D l n) : NativeL2.WeilModule D l (pointModel D) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (free D l n)
    (CondensedRing.upperStarFiniteFreeIso (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius (pointModel D)).hom n ≪≫ t)
/-- The constructed free Weil object's scalar-normalized Frobenius matrix is exactly
that of the supplied automorphism, also at rank zero.
Source: latest blueprint, dimension-zero Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-free-automorphism).
Proof: expand the fixed pair's structure isomorphism. In the identity basis, its
Frobenius comparison is immediately followed by its inverse. The pullback of the
identity is the identity, so cancellation leaves the supplied automorphism. -/
theorem freeWeilObject_matrix (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (t : free D l n ≅ free D l n) :
    frobeniusMatrix D l (freeWeilObject D l n t) (Iso.refl _) = matrix D l t.hom := by
  unfold frobeniusMatrix freeWeilObject
  rw [CategoryTheory.Endofunctor.IsoAlgebra.mk_str]
  simp only [Iso.refl_inv, Iso.trans_hom, Iso.refl_hom, Category.comp_id]
  congr 1
  change _ ≫ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius (pointModel D)).hom).map (𝟙 (free D l n)) ≫ _ ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
end WeilConjectures.CondensedWeilPointFlags
