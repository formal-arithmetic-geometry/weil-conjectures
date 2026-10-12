/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.CategoryTheory.SiteCohomologyPullbackData
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Existence of normalized pullback on object cohomology

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB; Sites, Tag 08J6.
(blueprint: lem-weil-pbc-site-cohomology-pullback-exists)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private noncomputable def freePresheafLift {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    (a : A.obj.obj (op V)) : yoneda.obj V ⋙ AddCommGrpCat.free ⟶ A.obj where
  app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun f ↦ (A.obj.map f.op).hom a))
  naturality {X Y} f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    simp [← Functor.map_comp, ← AddCommGrpCat.comp_apply]

private noncomputable def freeSheafLift {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    (a : A.obj.obj (op V)) :
    (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A :=
  ⟨sheafifyLift J (freePresheafLift J V A a) A.property⟩

private theorem freeSheafLift_eval {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (V : C) (A : Sheaf J AddCommGrpCat.{u})
    (a : A.obj.obj (op V)) :
    ((freeSheafLift J V A a).hom.app (op V)).hom
      (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
        (FreeAbelianGroup.of (𝟙 V))) = a := by
  have h := toSheafify_sheafifyLift J (freePresheafLift J V A a) A.property
  have hh := congrArg (fun f ↦ (f.app (op V)).hom (FreeAbelianGroup.of (𝟙 V))) h
  change ((sheafifyLift J (freePresheafLift J V A a) A.property).app (op V)).hom
    (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
      (FreeAbelianGroup.of (𝟙 V))) = a
  change _ = (FreeAbelianGroup.lift (fun f ↦ (A.obj.map f.op).hom a))
    (FreeAbelianGroup.of (𝟙 V)) at hh
  have hr : (FreeAbelianGroup.lift (fun f ↦ (A.obj.map f.op).hom a))
      (FreeAbelianGroup.of (𝟙 V)) = a := by simp
  exact hh.trans hr

private noncomputable def pullbackGenerator {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] (V : C) :
    (presheafToSheaf K AddCommGrpCat.{u}).obj
        (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free) ⟶
      (sheafPullback U AddCommGrpCat.{u} J K).obj
        ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free)) :=
  freeSheafLift K (U.obj V) _
    ((((sheafAdjunctionContinuous U AddCommGrpCat.{u} J K).unit.app
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free))).hom.app
        (op V)).hom
      (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
        (FreeAbelianGroup.of (𝟙 V))))

private noncomputable def pullbackFamily {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] [(sheafPullback U AddCommGrpCat.{u} J K).Additive]
    [PreservesFiniteLimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [PreservesFiniteColimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})] :
    SiteCohomologyFamily J K U := fun p V A ↦
  AddCommGrpCat.ofHom
    (((Abelian.Ext.mk₀ (pullbackGenerator J K U V)).precomp _ (zero_add p)).comp
      ((sheafPullback U AddCommGrpCat.{u} J K).mapExtAddHom _ A p))

/-- An exact inverse image admits a natural, normalized map commuting with boundaries.

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB; Sites, Tag 08J6.
(blueprint: lem-weil-pbc-site-cohomology-pullback-exists)

Proof: Let P(V) be the sheafification of the free abelian representable on V.
The generator of P(V) corresponds by the inverse-image adjunction to a section of
f⁻¹P(V) over U(V). The free-abelian and sheafification adjunctions give a map
b : P(U(V)) → f⁻¹P(V) representing that section. Define the map on Ext by applying
the exact functor f⁻¹ to an extension class and then precomposing with b.
Exact functors preserve Yoneda products, degree-zero morphisms, and the class of a
short exact sequence (Mathlib Ext.mapExactFunctor_comp, mapExactFunctor_mk₀,
mapExactFunctor_extClass). Associativity of Yoneda composition then proves
naturality and boundary compatibility. In degree zero the construction is f⁻¹(a)
b, whose value on the universal generator is the unit applied to the value of a;
this follows from naturality of the adjunction unit. Hence all three clauses hold.
This statement only constructs a family; uniqueness is proved separately. -/
theorem siteCohomology_pullback_exists {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] [(sheafPullback U AddCommGrpCat.{u} J K).Additive]
    [PreservesFiniteLimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [PreservesFiniteColimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})] :
    ∃ f : SiteCohomologyFamily J K U, SiteCohomologyFamily.IsPullback J K U f := by
  refine ⟨pullbackFamily J K U, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p V A B φ
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change (Abelian.Ext.mk₀ (pullbackGenerator J K U V)).comp
      ((x.comp (Abelian.Ext.mk₀ φ) (add_zero p)).mapExactFunctor
        (sheafPullback U AddCommGrpCat.{u} J K)) (zero_add p) =
      ((Abelian.Ext.mk₀ (pullbackGenerator J K U V)).comp
        (x.mapExactFunctor (sheafPullback U AddCommGrpCat.{u} J K)) (zero_add p)).comp
          (Abelian.Ext.mk₀ ((sheafPullback U AddCommGrpCat.{u} J K).map φ)) (add_zero p)
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add p) (add_zero p)
      (by simp)).symm
  · intro S hS hS' p V x
    change (Abelian.Ext.mk₀ (pullbackGenerator J K U V)).comp
      ((x.comp hS.extClass rfl).mapExactFunctor
        (sheafPullback U AddCommGrpCat.{u} J K)) (zero_add (p + 1)) =
      ((Abelian.Ext.mk₀ (pullbackGenerator J K U V)).comp
        (x.mapExactFunctor (sheafPullback U AddCommGrpCat.{u} J K)) (zero_add p)).comp
          hS'.extClass rfl
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add p) rfl (by simp)).symm
  · intro V A x
    let F := sheafPullback U AddCommGrpCat.{u} J K
    let a := Abelian.Ext.addEquiv₀ x
    have hx : x = Abelian.Ext.mk₀ a := (Abelian.Ext.mk₀_addEquiv₀_apply x).symm
    have hy : Abelian.Ext.addEquiv₀ ((pullbackFamily J K U 0 V A).hom x) =
        pullbackGenerator J K U V ≫ F.map a := by
      apply (Abelian.Ext.mk₀_bijective _ (F.obj A)).injective
      rw [Abelian.Ext.mk₀_addEquiv₀_apply]
      change (Abelian.Ext.mk₀ (pullbackGenerator J K U V)).comp
        (x.mapExactFunctor F) (zero_add 0) = _
      rw [hx, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    dsimp only [Sheaf.objectCohomologyEval₀]
    rw [hy]
    change (F.map a).hom.app (op (U.obj V))
      (((pullbackGenerator J K U V).hom.app (op (U.obj V))).hom
        (((toSheafify K (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free)).app
          (op (U.obj V))).hom (FreeAbelianGroup.of (𝟙 (U.obj V))))) = _
    rw [pullbackGenerator, freeSheafLift_eval]
    have hn := (sheafAdjunctionContinuous U AddCommGrpCat.{u} J K).unit.naturality a
    have he := congrArg (fun f ↦ (f.hom.app (op V)).hom
      (((toSheafify J (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
        (FreeAbelianGroup.of (𝟙 V)))) hn
    exact he.symm

end CategoryTheory
