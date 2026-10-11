/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The pushforward of Weil sheaves along the identity

The pushforward `(𝟙 X)_*` of pro-étale Weil sheaves along the identity of a `k₀`-scheme `X` is
the pushforward along the base change `𝟙 X̄`, which is the identity, with the transported Weil
structure; the unit laws for the composition isomorphisms of pushforwards show that the
transported Weil structure is the original one.

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarIdIso`: `(𝟙 X)_* ≅ 𝟭` on pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.lowerStarIdIso`: `(𝟙 X)_* ≅ 𝟭` on Weil sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open ProEtale Endofunctor

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

/-- The unit laws for the composition isomorphisms of the pushforwards of sheaves of
`ℚ̄_ℓ,Y`-modules, in the form of an exchange with an endomorphism `t` of `Y`: the composite
`(𝟙 ≫ t)_* ≅ (t ≫ 𝟙)_*` of the composition isomorphisms is the pushforward along `t` of the
identification `(𝟙 Y)_* ≅ 𝟭`. -/
lemma adicLowerStarId_exchange (t : Y ⟶ Y) (h : 𝟙 Y ≫ t = t ≫ 𝟙 Y) (M : AdicSheaf l Y) :
    (t)_*ᵃ[l].map ((adicLowerStarId l Y).hom.app M) =
      (adicLowerStarComp l (𝟙 Y) t).hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l t (𝟙 Y)).inv.app M ≫
          (adicLowerStarId l Y).hom.app ((t)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarId_hom_app_hom]
  rw [lowerStarComp_id_left_hom_app, lowerStarComp_id_right]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc,
    lowerStarCongr, eqToIso.hom, eqToHom_refl]
  erw [Iso.inv_hom_id_app, Category.comp_id]

/-- `AlgebraicGeometry.ProEtale.adicLowerStarId_exchange` for an endomorphism `g` equal to the
identity. -/
lemma adicLowerStarCongrId_exchange {g t : Y ⟶ Y} (hg : g = 𝟙 Y) (h : g ≫ t = t ≫ g)
    (M : AdicSheaf l Y) :
    (t)_*ᵃ[l].map ((adicLowerStarCongr l hg).hom.app M ≫ (adicLowerStarId l Y).hom.app M) =
      (adicLowerStarComp l g t).hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l t g).inv.app M ≫ (adicLowerStarCongr l hg).hom.app ((t)_*ᵃ[l].obj M) ≫
          (adicLowerStarId l Y).hom.app ((t)_*ᵃ[l].obj M) := by
  subst hg
  have e (N : AdicSheaf l Y) : (adicLowerStarCongr l (rfl : 𝟙 Y = 𝟙 Y)).hom.app N = 𝟙 _ :=
    Mod.hom_ext _ _ (by rw [adicLowerStarCongr_hom_app_hom, lowerStarCongr_rfl]; rfl)
  simp only [e, Category.id_comp]
  exact adicLowerStarId_exchange t h M

end ProEtale

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The pushforward of a Weil sheaf along the identity is the Weil sheaf itself: the underlying
sheaf is the pushforward along `𝟙 X̄`, and the unit laws for the composition isomorphisms of
pushforwards identify the transported Weil structure with the original one
(`AlgebraicGeometry.ProEtale.adicLowerStarCongrId_exchange`). -/
noncomputable def lowerStarIdIso (F : WeilSheaf k₀ l X) : (lowerStar (𝟙 X)).obj F ≅ F :=
  ObjectProperty.isoMk _ (IsoAlgebra.isoMk
    ((adicLowerStarCongr l Scheme.Hom.geometricFiberMap_id ≪≫ adicLowerStarId l _).app
      F.obj.carrier) (by
      have hstr := congrArg Iso.hom (lowerStar_obj_obj_str (𝟙 X) F)
      simp only [Iso.trans_hom] at hstr
      refine Eq.trans ?_ (congrArg (· ≫ _) hstr.symm)
      rw [Functor.mapIso_hom, Category.assoc]
      erw [(adicLowerStarCongr l Scheme.Hom.geometricFiberMap_id ≪≫
        adicLowerStarId l _).hom.naturality F.obj.str.hom]
      rw [Functor.id_map, ← Category.assoc]
      congr 1
      simp only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
        adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.symm_hom, Category.assoc]
      exact adicLowerStarCongrId_exchange _ _ _))

end WeilSheaf

end AlgebraicGeometry
