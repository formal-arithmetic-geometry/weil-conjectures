/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Factorisation isomorphisms of `ℓ`-adic pullbacks

For a factorisation `b ≫ c = a` of morphisms of schemes, the pullbacks of `ℓ`-adic sheaves
satisfy `a^* ≅ c^* ⋙ b^*` (`AlgebraicGeometry.ProEtale.adicUpperStarFactor`). These isomorphisms
are associative (`AlgebraicGeometry.ProEtale.adicUpperStarFactor_inv_app_assoc`): the equations
of the factorisations are arbitrary hypotheses, so that the identities can be instantiated at
concrete morphisms without unfolding them.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

variable (l) in
/-- The factorisation isomorphism `a^* ≅ c^* ⋙ b^*` of `ℓ`-adic pullbacks along a factorisation
`b ≫ c = a`. -/
noncomputable def adicUpperStarFactor {P Y Z : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) : (a)^*ᵃ[l] ≅ (c)^*ᵃ[l] ⋙ (b)^*ᵃ[l] :=
  adicUpperStarCongr l e.symm ≪≫ adicUpperStarComp l b c

lemma adicUpperStarFactor_hom_app_hom {P Y Z : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (M : AdicSheaf l Y) :
    ((adicUpperStarFactor l e).hom.app M).hom =
      (upperStarFactor (WeilCoefficients.{u} l) e).hom.app M.X := by
  simp only [adicUpperStarFactor, upperStarFactor, Iso.trans_hom, NatTrans.comp_app,
    Mod.comp_hom', adicUpperStarCongr_hom_app_hom, adicUpperStarComp_hom_app_hom]

/-- The inverse of a factorisation isomorphism is the inverse of the composition isomorphism
followed by the congruence isomorphism. -/
lemma adicUpperStarFactor_inv_app {P Y Z : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (M : AdicSheaf l Y) :
    (adicUpperStarFactor l e).inv.app M =
      (adicUpperStarComp l b c).inv.app M ≫ (adicUpperStarCongr l e).hom.app M := by
  subst e
  simp [adicUpperStarFactor, adicUpperStarCongr]

/-- The trivial factorisation isomorphism is the composition isomorphism. -/
lemma adicUpperStarFactor_rfl {P Y Z : Scheme.{u}} (b : P ⟶ Z) (c : Z ⟶ Y) :
    adicUpperStarFactor l (rfl : b ≫ c = b ≫ c) = adicUpperStarComp l b c := by
  simp [adicUpperStarFactor, adicUpperStarCongr]

/-- **Associativity of the factorisation isomorphisms** of `ℓ`-adic pullbacks. -/
lemma adicUpperStarFactor_hom_app_assoc {P'' P' Z Y : Scheme.{u}} {a : P'' ⟶ Y} {x : P'' ⟶ P'}
    {y : P' ⟶ Z} {z : Z ⟶ Y} {b : P' ⟶ Y} {c : P'' ⟶ Z} (e_b : y ≫ z = b) (e_a : x ≫ b = a)
    (e_c : x ≫ y = c) (e_a' : c ≫ z = a) (M : AdicSheaf l Y) :
    (adicUpperStarFactor l e_a).hom.app M ≫ (x)^*ᵃ[l].map ((adicUpperStarFactor l e_b).hom.app M) =
      (adicUpperStarFactor l e_a').hom.app M ≫
        (adicUpperStarFactor l e_c).hom.app ((z)^*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarFactor_hom_app_hom]
  exact upperStarFactor_hom_app_assoc _ e_b e_a e_c e_a' M.X

/-- **Associativity of the factorisation isomorphisms** of `ℓ`-adic pullbacks, for the inverse
isomorphisms. -/
lemma adicUpperStarFactor_inv_app_assoc {P'' P' Z Y : Scheme.{u}} {a : P'' ⟶ Y} {x : P'' ⟶ P'}
    {y : P' ⟶ Z} {z : Z ⟶ Y} {b : P' ⟶ Y} {c : P'' ⟶ Z} (e_b : y ≫ z = b) (e_a : x ≫ b = a)
    (e_c : x ≫ y = c) (e_a' : c ≫ z = a) (M : AdicSheaf l Y) :
    (x)^*ᵃ[l].map ((adicUpperStarFactor l e_b).inv.app M) ≫
        (adicUpperStarFactor l e_a).inv.app M =
      (adicUpperStarFactor l e_c).inv.app ((z)^*ᵃ[l].obj M) ≫
        (adicUpperStarFactor l e_a').inv.app M := by
  rw [← cancel_epi ((adicUpperStarFactor l e_c).hom.app ((z)^*ᵃ[l].obj M)),
    ← cancel_epi ((adicUpperStarFactor l e_a').hom.app M),
    ← reassoc_of% adicUpperStarFactor_hom_app_assoc e_b e_a e_c e_a' M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app]

end AlgebraicGeometry.ProEtale
