/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ModuleSheafSmul
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Sections

/-!
# The comparison of the two finite-coefficient models commutes with pullback

Let `T` be a finite discrete commutative ring and `Φ_X = finiteCoefficientModEquivalence X T` the
identification of module objects over `Λ_X = p_X^* T̲` with sheaves of `T`-modules on `X_proét`.
For a morphism of schemes `g : W ⟶ X` and a `Λ_X`-module `N` there is an isomorphism
```
g^* (Φ_X N) ≅ Φ_W (g^* N)
```
between the pullback of sheaves of `T`-modules and the image of the pullback of module objects
(`AlgebraicGeometry.ProEtale.finiteCoefficientModEquivalenceUpperStarIso`). Both have the
underlying abelian sheaf `g^* N` (the pullback commutes with the forgetful functor to abelian
sheaves, `AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso`), and the actions of
`t ∈ T` agree: on `Φ_X N` it is the action of the constant global section `t` of `Λ_X`
(`AlgebraicGeometry.ProEtale.finiteCoefficientModEquivalence_smul`), and the constant global
sections are compatible with pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

/-! ### Actions of global sections on module objects -/

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] {A : C} [MonObj A]

/-- Morphisms of module objects commute with the actions of global sections. -/
@[reassoc]
lemma globalSmul_comp_hom (σ : 𝟙_ C ⟶ A) {M N : Mod C A} (f : M ⟶ N) :
    globalSmul σ M ≫ f.hom = f.hom ≫ globalSmul σ N := by
  rw [globalSmul, globalSmul, Category.assoc, Category.assoc, act_hom, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

/-- The action of a global section `σ` on the image of a module object under a lax monoidal
functor `F` is the image of the action: `ε ≫ F σ` acts on `F M` as `F (σ •)`. -/
lemma globalSmul_mapMod {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] (σ : 𝟙_ C ⟶ A) (M : Mod C A) :
    globalSmul (ε F ≫ F.map σ) ((F.mapMod A).obj M) = F.map (globalSmul σ M) := by
  rw [globalSmul, globalSmul, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc]
  erw [Functor.act_mapMod_obj, comp_whiskerRight, Category.assoc, μ_natural_left_assoc]
  rfl

/-- The unit section, followed by the action of a global section `σ` on the regular module, is
`σ`. -/
lemma one_comp_globalSmul_regular (σ : 𝟙_ C ⟶ A) : η[A] ≫ globalSmul σ (regular A) = σ := by
  have h : regularLift (regular A) η[A] = 𝟙 _ :=
    regular_hom_ext ((one_comp_regularLift (regular A) η[A]).trans (Category.comp_id _).symm)
  have h' := comp_regularLift_hom σ (regular A) η[A]
  rw [h, id_hom'] at h'
  exact h'.symm.trans (Category.comp_id σ)

/-- Let `F` be lax monoidal, `α : F A ⟶ B` a morphism of monoid objects and `κ : F N ⟶ P` a
morphism of `F A`-modules, `P` a `B`-module. If the global section `σ'` of `B` is the image of
the global section `σ` of `A`, then `κ` intertwines `F (σ •)` and `σ' •`. -/
lemma map_globalSmul_comp_hom {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {B : D} [MonObj B] (α : F.obj A ⟶ B) [IsMonHom α] (σ : 𝟙_ C ⟶ A)
    (σ' : 𝟙_ D ⟶ B) (hσ : (ε F ≫ F.map σ) ≫ α = σ') (N : Mod C A) (P : Mod D B)
    (κ : (F.mapMod A).obj N ⟶ (comap α).obj P) :
    F.map (globalSmul σ N) ≫ κ.hom = κ.hom ≫ globalSmul σ' P := by
  rw [← globalSmul_mapMod, globalSmul_comp_hom, globalSmul_comap, hσ]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The constant global section `t` of `Λ_X = p_X^* T̲`: the image under `p_X^*` of the constant
global section of `T̲`. -/
noncomputable abbrev constSection (X : Scheme.{u}) (t : T) :
    Γ (condensedRingObj (Profinite.continuousMapRingObj.{u} T) X) :=
  Γ.mapFunctor (upperStarFromPoint X) (Profinite.continuousMapConstRingHom.{u} T t)

omit [Finite T] in
/-- The constant global sections are compatible with pullback. -/
lemma Γ_map_condensedPullbackHom_constSection {W X : Scheme.{u}} (g : W ⟶ X) (t : T) :
    Γ.map (condensedPullbackHom (Profinite.continuousMapRingObj.{u} T) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (constSection X t)) = constSection W t := by
  rw [constSection, constSection, ← finiteSectionRingHom_const, ← finiteSectionRingHom_const,
    Γ_map_condensedPullbackHom_finiteSectionRingHom]
  rfl

/-- **The scalars of `finiteCoefficientModEquivalence`**, on underlying abelian sheaves: the
multiplication by `t ∈ T` on the sheaf of `T`-modules corresponding to a `Λ_X`-module `M` is the
action on `M` of the constant global section `t`. -/
lemma sheafCompose_map_smulEnd_finiteCoefficientModEquivalence {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) (t : T) :
    (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).map
      (Sheaf.smulEnd (ULift.up t) ((finiteCoefficientModEquivalence X T).functor.obj M)) =
      Mod.globalSmul (constSection X t).hom M := by
  ext U y
  exact finiteCoefficientModEquivalence_smul X T M U t y

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- The pullback of sheaves of `T`-modules commutes with the multiplications by `r`. -/
lemma upperStar_map_smulEnd {W X : Scheme.{u}} (g : W ⟶ X) (r : ULift.{u + 1} T)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :
    (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map (Sheaf.smulEnd r F) =
      Sheaf.smulEnd r ((g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj F) :=
  Sheaf.map_smulEnd_of_adjunction (upperStarLowerStarAdjunction _ g) (fun _ _ ↦ rfl) r F

omit [Finite T] in
/-- The action of the constant global section `t` commutes with the identification
`j^* M ≅ j^* M` of the sheaf pullback of a module object with the pullback of module objects
(`ProEtale.CondensedRing.comapUpperStarObjIso`). -/
lemma upperStar_map_globalSmul_comp_comapUpperStarObjIso_inv {W X : Scheme.{u}} (g : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) (t : T) :
    (g)^*[Ab.{u + 1}].map (Mod.globalSmul (constSection X t).hom N) ≫
        (comapUpperStarObjIso (Profinite.continuousMapRingObj.{u} T) g N).inv.hom =
      (comapUpperStarObjIso (Profinite.continuousMapRingObj.{u} T) g N).inv.hom ≫
        Mod.globalSmul (constSection W t).hom
          ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj N) :=
  Mod.map_globalSmul_comp_hom _ _ _ _
    (congrArg Γ.hom (Γ_map_condensedPullbackHom_constSection g t))
    N _ _

/-- **The comparison `Φ` commutes with pullback**: for `g : W ⟶ X` and a `Λ_X`-module `N`, the
pullback of the sheaf of `T`-modules `Φ_X N` is `Φ_W (g^* N)`. -/
noncomputable def finiteCoefficientModEquivalenceUpperStarIso {W X : Scheme.{u}} (g : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        ((finiteCoefficientModEquivalence X T).functor.obj N) ≅
      (finiteCoefficientModEquivalence W T).functor.obj
        ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj N) :=
  Sheaf.isoOfSheafComposeForget₂Iso.{u + 1, u, u + 1} (J := Scheme.ProEt.topology W)
    (((sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} T) g).app
      ((finiteCoefficientModEquivalence X T).functor.obj N)).symm ≪≫
      (Mod.forget _).mapIso
        (CondensedRing.comapUpperStarObjIso (Profinite.continuousMapRingObj.{u} T) g N).symm)
    fun r ↦ by
      obtain ⟨t⟩ := r
      have nat := (sheafComposeForget₂CompUpperStarIso (ULift.{u + 1} T) g).inv.naturality
        (Sheaf.smulEnd (ULift.up t) ((finiteCoefficientModEquivalence X T).functor.obj N))
      dsimp only [Functor.comp_obj, Functor.comp_map] at nat
      rw [upperStar_map_smulEnd, sheafCompose_map_smulEnd_finiteCoefficientModEquivalence] at nat
      have h₂ := upperStar_map_globalSmul_comp_comapUpperStarObjIso_inv g N t
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Mod.forget_map,
        Category.assoc]
      rw [reassoc_of% nat, sheafCompose_map_smulEnd_finiteCoefficientModEquivalence, h₂]

end AlgebraicGeometry.ProEtale
