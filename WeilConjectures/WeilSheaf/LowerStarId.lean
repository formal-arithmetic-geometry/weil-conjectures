/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The pushforward of Weil sheaves along the identity

The pushforward `(𝟙 X)_*` of Weil sheaves along the identity of `X` is isomorphic to the identity:
on the underlying sheaves it is the pushforward along the base change `𝟙 X̄`, and the unit law
of the composition isomorphisms of pushforwards makes the identification `(𝟙 X̄)_* ≅ 𝟭`
compatible with the Weil structures.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.lowerStarIdIso`: `(𝟙 X)_* F ≅ F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

universe u'

variable {A : Type u'} [Category.{u + 1} A] {Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
-- the components are computed by `simp` before the pullback isomorphisms are unfolded
set_option linter.flexible false in
/-- The identification `p_* ≅ 𝟭` for `p = 𝟙` commutes with the exchange isomorphism
`p_* ⋙ a_* ≅ a_* ⋙ p_*` of the square `p ≫ a = a ≫ p`. -/
lemma lowerStar_map_lowerStarCongr_comp_lowerStarId {p a : Z ⟶ Z} (hp : p = 𝟙 Z)
    (h : p ≫ a = a ≫ p) (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (a)_*[A].map ((lowerStarCongr A hp).hom.app M ≫ (lowerStarId A Z).hom.app M) =
      (lowerStarComp A p a).hom.app M ≫ (lowerStarCongr A h).hom.app M ≫
        (lowerStarComp A a p).inv.app M ≫ (lowerStarCongr A hp).hom.app ((a)_*[A].obj M) ≫
          (lowerStarId A Z).hom.app ((a)_*[A].obj M) := by
  subst hp
  ext V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStarComp_inv_app_hom_app,
    lowerStarComp_hom_app_hom_app, lowerStar_map_hom_app', lowerStarId_hom_app_hom_app,
    lowerStar_obj_obj_map', ObjectProperty.FullSubcategory.id_hom]
  erw [Category.id_comp (M.obj.map _)]
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]
      erw [pullbackLeftPullbackSndIso_hom_fst]
      simp
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]
      erw [pullbackLeftPullbackSndIso_hom_snd]
      simp
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]
    erw [pullbackLeftPullbackSndIso_hom_snd]
    simp

variable {l : ℕ} [Fact l.Prime]

/-- `AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarCongr_comp_lowerStarId` for sheaves of
`ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_map_adicLowerStarCongr_comp_adicLowerStarId {p a : Z ⟶ Z} (hp : p = 𝟙 Z)
    (h : p ≫ a = a ≫ p) (M : AdicSheaf l Z) :
    (a)_*ᵃ[l].map ((adicLowerStarCongr l hp).hom.app M ≫ (adicLowerStarId l Z).hom.app M) =
      (adicLowerStarComp l p a).hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l a p).inv.app M ≫
          (adicLowerStarCongr l hp).hom.app ((a)_*ᵃ[l].obj M) ≫
            (adicLowerStarId l Z).hom.app ((a)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarId_hom_app_hom]
  exact lowerStar_map_lowerStarCongr_comp_lowerStarId hp h M.X

/-- The identification `p_* ≅ 𝟭` for `p = 𝟙` is compatible with any morphism
`s : a_* M ⟶ M`, transported along the exchange isomorphism of the square `p ≫ a = a ≫ p`. -/
lemma adicLowerStar_map_comp_eq {p a : Z ⟶ Z} (hp : p = 𝟙 Z) (h : p ≫ a = a ≫ p)
    {M : AdicSheaf l Z} (s : (a)_*ᵃ[l].obj M ⟶ M) :
    (a)_*ᵃ[l].map ((adicLowerStarCongr l hp ≪≫ adicLowerStarId l Z).hom.app M) ≫ s =
      ((adicLowerStarComp l p a ≪≫ adicLowerStarCongr l h ≪≫
        (adicLowerStarComp l a p).symm).hom.app M ≫ (p)_*ᵃ[l].map s) ≫
        (adicLowerStarCongr l hp ≪≫ adicLowerStarId l Z).hom.app M := by
  have hn := (adicLowerStarCongr l hp ≪≫ adicLowerStarId l Z).hom.naturality s
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.id_map, Iso.symm_hom,
    Category.assoc] at hn ⊢
  rw [hn, adicLowerStar_map_adicLowerStarCongr_comp_adicLowerStarId hp h]
  simp only [Category.assoc, Functor.id_obj]

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

open Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The pushforward of a Weil sheaf along the identity is the Weil sheaf itself: the
identification `(𝟙 X̄)_* ≅ 𝟭` of the underlying sheaves is compatible with the Weil
structures. -/
noncomputable def lowerStarIdIso (F : WeilSheaf k₀ l X) :
    (WeilSheaf.lowerStar (𝟙 X)).obj F ≅ F :=
  have hg := Scheme.Hom.geometricFiberMap_id (f := X ↘ Spec (CommRingCat.of k₀))
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Algebra.isoMk
    ((ProEtale.adicLowerStarCongr l hg ≪≫ ProEtale.adicLowerStarId l _).app F.obj.carrier)
    (ProEtale.adicLowerStar_map_comp_eq hg _ F.obj.str.hom)))

end AlgebraicGeometry.WeilSheaf
