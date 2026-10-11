/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The pushforward of pro-étale Weil sheaves along the identity

The pushforward `(𝟙 X)_*` of pro-étale Weil sheaves is the identity functor
(`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarIdIso`): the base change of `𝟙 X` is the
identity of `X̄`, and the identification `(𝟙 X̄)_* ≅ 𝟭` is compatible with the exchange
isomorphism defining the Weil structure of a pushforward.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

open Scheme

/-- The exchange isomorphism `g_* ⋙ a_* ≅ a_* ⋙ g_*` for an endomorphism `g = 𝟙` commuting with
`a` is compatible with the identification `(𝟙)_* ≅ 𝟭`. -/
lemma lowerStar_map_lowerStarCongr_lowerStarId {A : Type u'} [Category.{u + 1} A]
    {Z : Scheme.{u}}
    {g : Z ⟶ Z} (h₀ : g = 𝟙 Z) (a : Z ⟶ Z) (h : g ≫ a = a ≫ g)
    (M : Sheaf (ProEt.topology Z) A) :
    (a)_*[A].map ((lowerStarCongr A h₀).hom.app M ≫ (lowerStarId A Z).hom.app M) =
      (lowerStarComp A g a).hom.app M ≫ (lowerStarCongr A h).hom.app M ≫
        (lowerStarComp A a g).inv.app M ≫ (lowerStarCongr A h₀).hom.app ((a)_*[A].obj M) ≫
          (lowerStarId A Z).hom.app ((a)_*[A].obj M) := by
  subst h₀
  rw [← NatTrans.comp_app_assoc, ← Iso.trans_hom, lowerStarComp_trans_lowerStarCongr]
  ext V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStarComp_inv_app_hom_app,
    lowerStar_map_hom_app', lowerStarId_hom_app_hom_app, lowerStarFactor_hom_app_hom_app,
    lowerStar_obj_obj_map', ObjectProperty.FullSubcategory.id_hom]
  erw [Category.id_comp (M.obj.map _)]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]
    apply pullback.hom_ext <;> simp
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]

/-- `AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarCongr_lowerStarId` for sheaves of
`ℚ̄_ℓ,X`-modules. -/
lemma adicLowerStar_map_adicLowerStarCongr_adicLowerStarId {l : ℕ} [Fact l.Prime]
    {Z : Scheme.{u}} {g : Z ⟶ Z} (h₀ : g = 𝟙 Z) (a : Z ⟶ Z) (h : g ≫ a = a ≫ g)
    (M : AdicSheaf l Z) :
    (a)_*ᵃ[l].map ((adicLowerStarCongr l h₀).hom.app M ≫ (adicLowerStarId l Z).hom.app M) =
      (adicLowerStarComp l g a).hom.app M ≫ (adicLowerStarCongr l h).hom.app M ≫
        (adicLowerStarComp l a g).inv.app M ≫
          (adicLowerStarCongr l h₀).hom.app ((a)_*ᵃ[l].obj M) ≫
            (adicLowerStarId l Z).hom.app ((a)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarComp_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarId_hom_app_hom]
  exact lowerStar_map_lowerStarCongr_lowerStarId h₀ a h M.X

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open Endofunctor in
variable (k₀ l X) in
/-- The pushforward of pro-étale Weil sheaves along the identity is the identity functor. -/
noncomputable def ProEtaleWeilSheaf.lowerStarIdIso :
    ProEtaleWeilSheaf.lowerStar k₀ l (𝟙 X) ≅ 𝟭 _ :=
  IsoAlgebra.mapOfNatIsoIsoOfIso
    (e' := (WeilSheaf.frobeniusPullback k₀ l X).leftUnitor ≪≫ Iso.refl _ ≪≫
      (WeilSheaf.frobeniusPullback k₀ l X).rightUnitor.symm)
    (ProEtale.adicLowerStarCongr l (Scheme.Hom.geometricFiberMap_id (f := X ↘ _)) ≪≫
      ProEtale.adicLowerStarId l _) (by
      ext M : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Iso.trans_hom, ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.symm_hom,
        Category.assoc, Iso.refl_hom, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
        Category.comp_id, Category.id_comp]
      exact ProEtale.adicLowerStar_map_adicLowerStarCongr_adicLowerStarId
        (Scheme.Hom.geometricFiberMap_id (f := X ↘ _))
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv (𝟙 X) _) M) ≪≫
    IsoAlgebra.twistReflIso

end AlgebraicGeometry
