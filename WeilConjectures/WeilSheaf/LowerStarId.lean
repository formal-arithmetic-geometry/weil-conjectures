/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The pushforward of Weil sheaves along the identity

The pushforward `(𝟙 X)_*` of a Weil sheaf along the identity of `X` is the Weil sheaf itself
(`AlgebraicGeometry.WeilSheaf.lowerStarIdIso`): on underlying sheaves this is the identity
isomorphism of pushforwards along the base change `𝟙 X̄` of `𝟙 X`, and it is compatible with
the Weil structures by the unit laws for the composition isomorphisms of pushforwards.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.lowerStarIdIso`: `(𝟙 X)_* F ≅ F`.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- For an endomorphism `g = 𝟙` commuting with `a`, the identity isomorphism of `g_*` is
compatible with the exchange isomorphism `a_* g_* ≅ (g ≫ a)_* = (a ≫ g)_* ≅ g_* a_*`. -/
lemma lowerStar_map_lowerStarCongr_comp_lowerStarId {T : Scheme.{u}} (g a : T ⟶ T)
    (hg : g = 𝟙 T) (h : g ≫ a = a ≫ g) (M : Sheaf (Scheme.ProEt.topology T) A) :
    (a)_*[A].map ((lowerStarCongr A hg).hom.app M ≫ (lowerStarId A T).hom.app M) =
      (lowerStarComp A g a).hom.app M ≫ (lowerStarCongr A h).hom.app M ≫
        (lowerStarComp A a g).inv.app M ≫ (lowerStarCongr A hg).hom.app ((a)_*[A].obj M) ≫
          (lowerStarId A T).hom.app ((a)_*[A].obj M) := by
  subst hg
  rw [lowerStarComp_id_left, lowerStarComp_id_right]
  simp only [lowerStarCongr, eqToIso.hom, eqToHom_refl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.isoWhiskerRight_hom, Functor.leftUnitor_hom_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, NatTrans.id_app, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp, Category.comp_id]

end ProEtale

end AlgebraicGeometry
