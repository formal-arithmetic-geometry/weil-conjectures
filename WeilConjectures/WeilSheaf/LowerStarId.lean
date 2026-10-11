/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence

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
  simp [lowerStarCongr]
  first
  | exact ((Category.comp_id _).symm.trans (congrArg _ (Category.id_comp _).symm))
  | (rw [Category.id_comp]; exact (Category.comp_id _).symm)
  | exact (Category.comp_id _).symm.trans (Category.comp_id _).symm
variable {l : ℕ} [Fact l.Prime]

/-- `AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarCongr_comp_lowerStarId` for sheaves of
`ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_map_adicLowerStarCongr_comp_adicLowerStarId {T : Scheme.{u}} (g a : T ⟶ T)
    (hg : g = 𝟙 T) (h : g ≫ a = a ≫ g) (M : AdicSheaf l T) :
    (a)_*ᵃ[l].map ((adicLowerStarCongr l hg).hom.app M ≫ (adicLowerStarId l T).hom.app M) =
      (adicLowerStarComp l g a).hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l a g).inv.app M ≫
          (adicLowerStarCongr l hg).hom.app ((a)_*ᵃ[l].obj M) ≫
            (adicLowerStarId l T).hom.app ((a)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarId_hom_app_hom]
  exact lowerStar_map_lowerStarCongr_comp_lowerStarId (WeilCoefficients.{u} l) g a hg h M.X

end ProEtale

namespace WeilSheaf

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The pushforward of a Weil sheaf along the identity is the Weil sheaf itself: on underlying
sheaves, the identity isomorphism of the pushforward along `𝟙 X̄`, the base change of `𝟙 X`. -/
noncomputable def lowerStarIdIso (F : WeilSheaf k₀ l X) : (lowerStar (𝟙 X)).obj F ≅ F :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Algebra.isoMk
    ((adicLowerStarCongr l (Scheme.Hom.geometricFiberMap_id (f := X ↘ Spec (CommRingCat.of k₀)))).app
        F.obj.carrier ≪≫ (adicLowerStarId l _).app F.obj.carrier) (by
      have key := adicLowerStar_map_adicLowerStarCongr_comp_adicLowerStarId _ _
        (Scheme.Hom.geometricFiberMap_id (f := X ↘ Spec (CommRingCat.of k₀)))
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv (𝟙 X)
          (comp_over (𝟙 X) _)) F.obj.carrier
      have hs := congrArg Iso.hom (lowerStar_obj_obj_str (𝟙 X) F)
      rw [IsoAlgebra.str_hom] at hs
      rw [hs, Iso.trans_hom, Iso.app_hom, Iso.app_hom, key]
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
        adicLowerStarGeometricFiberMapCompFrobeniusIso, NatTrans.comp_app, Category.assoc]
      simp)))

end WeilSheaf

end AlgebraicGeometry
