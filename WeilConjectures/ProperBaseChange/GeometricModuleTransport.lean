/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The underlying sheaf adjunction restricted to linear maps

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 and 03D7.
(blueprint: lem-weil-pbc-geometric-module-transport).
-/

@[expose] public section

universe u uC vC
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Helpers

attribute [local instance] sheafHasBinaryProduct

private noncomputable abbrev ringBase
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev moduleSets
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringBase R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable def linearLift
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}}
    {M N : SheafOfModules.{u} (ringBase R)}
    (α : (moduleSets R).obj M ⟶ (moduleSets R).obj N)
    (ha : ∀ W (x y : M.val.obj W), α.hom.app W (x + y) =
      (show N.val.obj W from α.hom.app W x) +
        (show N.val.obj W from α.hom.app W y))
    (hs : ∀ W (r : R.obj.obj W) (x : M.val.obj W), α.hom.app W (r • x) =
      r • (show N.val.obj W from α.hom.app W x)) : M ⟶ N where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := α.hom.app W
          map_add' := ha W
          map_smul' := hs W }
      naturality := by
        intro X Y f
        ext x
        exact CategoryTheory.congr_fun (α.hom.naturality f) x }

private noncomputable def sectionPair
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (X ⨯ Y).obj.obj W :=
  (prod.lift (CartesianMonoidalCategory.fst X Y)
    (CartesianMonoidalCategory.snd X Y)).hom.app W (x, y)

private theorem sectionPair_fst
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.fst : X ⨯ Y ⟶ X).hom.app W (sectionPair X Y W x y) = x := by
  exact congrArg (fun f : X ⊗ Y ⟶ X ↦ f.hom.app W (x, y))
    (prod.lift_fst (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem sectionPair_snd
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.snd : X ⨯ Y ⟶ Y).hom.app W (sectionPair X Y W x y) = y := by
  exact congrArg (fun f : X ⊗ Y ⟶ Y ↦ f.hom.app W (x, y))
    (prod.lift_snd (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem prodMap_fst_apply
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {X Y X' Y' : Sheaf J (Type u)} (f : X ⟶ X') (g : Y ⟶ Y')
    (W : Cᵒᵖ) (x : (X ⨯ Y).obj.obj W) :
    (prod.fst : X' ⨯ Y' ⟶ X').hom.app W ((prod.map f g).hom.app W x) =
      f.hom.app W ((prod.fst : X ⨯ Y ⟶ X).hom.app W x) :=
  congrArg (fun h : X ⨯ Y ⟶ X' ↦ h.hom.app W x) (prod.map_fst f g)

private theorem prodMap_snd_apply
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {X Y X' Y' : Sheaf J (Type u)} (f : X ⟶ X') (g : Y ⟶ Y')
    (W : Cᵒᵖ) (x : (X ⨯ Y).obj.obj W) :
    (prod.snd : X' ⨯ Y' ⟶ Y').hom.app W ((prod.map f g).hom.app W x) =
      g.hom.app W ((prod.snd : X ⨯ Y ⟶ Y).hom.app W x) :=
  congrArg (fun h : X ⨯ Y ⟶ Y' ↦ h.hom.app W x) (prod.map_snd f g)

private noncomputable abbrev ringSets
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R

private def addSpec
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}} (M : SheafOfModules.{u} (ringBase R))
    (a : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M) : Prop :=
  ∀ W x, a.hom.app W x =
    (show M.val.obj W from (prod.fst : _ ⟶ (moduleSets R).obj M).hom.app W x) +
      (show M.val.obj W from (prod.snd : _ ⟶ (moduleSets R).obj M).hom.app W x)

private def smulSpec
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}} (M : SheafOfModules.{u} (ringBase R))
    (a : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M) : Prop :=
  ∀ W x, a.hom.app W x =
    (show R.obj.obj W from (prod.fst : _ ⟶ ringSets R).hom.app W x) •
      (show M.val.obj W from (prod.snd : _ ⟶ (moduleSets R).obj M).hom.app W x)

private theorem linear_iff
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (M : SheafOfModules.{u} (ringBase R)) (N : SheafOfModules.{u} (ringBase S))
    (aM : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
    (aN : (moduleSets S).obj N ⨯ (moduleSets S).obj N ⟶ (moduleSets S).obj N)
    (sM : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
    (sN : ringSets S ⨯ (moduleSets S).obj N ⟶ (moduleSets S).obj N)
    (haM : addSpec M aM) (haN : addSpec N aN)
    (hsM : smulSpec M sM) (hsN : smulSpec N sN)
    (α : (moduleSets R).obj M ⟶ (moduleSets S).obj N) :
    (∃ f : M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj N, (moduleSets R).map f = α) ↔
      aM ≫ α = prod.map α α ≫ aN ∧
      sM ≫ α = prod.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u})).map c) α ≫ sN := by
  constructor
  · rintro ⟨f, rfl⟩
    constructor
    · ext W x
      change f.val.app W (aM.hom.app W x) =
        aN.hom.app W ((prod.map ((moduleSets R).map f)
          ((moduleSets R).map f)).hom.app W x)
      rw [haM, haN]
      erw [prodMap_fst_apply, prodMap_snd_apply]
      exact (f.val.app W).hom.map_add _ _
    · ext W x
      change f.val.app W (sM.hom.app W x) =
        sN.hom.app W ((prod.map ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).map c)
          ((moduleSets R).map f)).hom.app W x)
      rw [hsM, hsN]
      erw [prodMap_fst_apply, prodMap_snd_apply]
      exact (f.val.app W).hom.map_smul _ _
  · rintro ⟨ha, hs⟩
    have hAdd W (x y : M.val.obj W) : α.hom.app W (x + y) =
        (show N.val.obj W from α.hom.app W x) +
          (show N.val.obj W from α.hom.app W y) := by
      let p := sectionPair ((moduleSets R).obj M) ((moduleSets R).obj M) W x y
      have h := congrArg (fun f ↦ f.hom.app W p) ha
      change α.hom.app W (aM.hom.app W p) =
        aN.hom.app W ((prod.map α α).hom.app W p) at h
      rw [haM, haN, prodMap_fst_apply, prodMap_snd_apply] at h
      simp only [p, sectionPair_fst, sectionPair_snd] at h
      exact h
    have hSmul W (r : R.obj.obj W) (x : M.val.obj W) : α.hom.app W (r • x) =
        (c.hom.app W r) • (show N.val.obj W from α.hom.app W x) := by
      let p := sectionPair (ringSets R) ((moduleSets R).obj M) W r x
      have h := congrArg (fun f ↦ f.hom.app W p) hs
      change α.hom.app W (sM.hom.app W p) =
        sN.hom.app W ((prod.map ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).map c) α).hom.app W p) at h
      rw [hsM, hsN, prodMap_fst_apply, prodMap_snd_apply] at h
      simp only [p, sectionPair_fst, sectionPair_snd] at h
      exact h
    exact ⟨linearLift α hAdd hSmul, rfl⟩

private theorem product_mate
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts V]
    {X₁ X₂ : C₀} {Y₁ Y₂ : D₀}
    (f₁ : L.obj X₁ ⟶ Y₁) (f₂ : L.obj X₂ ⟶ Y₂) :
    adj.homEquiv (X₁ ⨯ X₂) (Y₁ ⨯ Y₂)
        (prodComparison L X₁ X₂ ≫ prod.map f₁ f₂) =
      prod.map (adj.homEquiv X₁ Y₁ f₁) (adj.homEquiv X₂ Y₂ f₂) ≫
        inv (prodComparison V Y₁ Y₂) := by
  apply (cancel_mono (prodComparison V Y₁ Y₂)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simp only [prodComparison_fst, prod.map_fst]
    rw [← adj.homEquiv_naturality_right]
    simp only [Category.assoc, prod.map_fst, prodComparison_fst_assoc]
    exact adj.homEquiv_naturality_left _ _
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simp only [prodComparison_snd, prod.map_snd]
    rw [← adj.homEquiv_naturality_right]
    simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc]
    exact adj.homEquiv_naturality_left _ _

private theorem binary_mate_iff
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts V]
    {X₁ X₂ X₃ : C₀} {Y₁ Y₂ Y₃ : D₀}
    (a : X₁ ⨯ X₂ ⟶ X₃) (b : Y₁ ⨯ Y₂ ⟶ Y₃)
    (f₁ : L.obj X₁ ⟶ Y₁) (f₂ : L.obj X₂ ⟶ Y₂)
    (f₃ : L.obj X₃ ⟶ Y₃) :
    L.map a ≫ f₃ = prodComparison L X₁ X₂ ≫ prod.map f₁ f₂ ≫ b ↔
      a ≫ adj.homEquiv X₃ Y₃ f₃ =
        prod.map (adj.homEquiv X₁ Y₁ f₁) (adj.homEquiv X₂ Y₂ f₂) ≫
          inv (prodComparison V Y₁ Y₂) ≫ V.map b := by
  rw [← (adj.homEquiv (X₁ ⨯ X₂) Y₃).injective.eq_iff]
  rw [adj.homEquiv_naturality_left, ← Category.assoc,
    adj.homEquiv_naturality_right, product_mate]
  simp only [Category.assoc]

private theorem binary_mate_iso_iff
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts L] [PreservesFiniteProducts V]
    {X₁ X₂ X₃ P₁ P₂ P₃ : C₀} {I₁ I₂ I₃ Y₁ Y₂ Y₃ : D₀}
    (e₁ : I₁ ≅ L.obj X₁) (e₂ : I₂ ≅ L.obj X₂) (e₃ : I₃ ≅ L.obj X₃)
    (p₁ : P₁ ⟶ V.obj Y₁) (p₂ : P₂ ⟶ V.obj Y₂) (p₃ : P₃ ≅ V.obj Y₃)
    (a : X₁ ⨯ X₂ ⟶ X₃) (aI : I₁ ⨯ I₂ ⟶ I₃)
    (b : Y₁ ⨯ Y₂ ⟶ Y₃) (bP : P₁ ⨯ P₂ ⟶ P₃)
    (hL : L.map a = prodComparison L X₁ X₂ ≫
      prod.map e₁.inv e₂.inv ≫ aI ≫ e₃.hom)
    (hV : bP ≫ p₃.hom = prod.map p₁ p₂ ≫
      inv (prodComparison V Y₁ Y₂) ≫ V.map b)
    (α₁ : I₁ ⟶ Y₁) (α₂ : I₂ ⟶ Y₂) (α₃ : I₃ ⟶ Y₃)
    (β₁ : X₁ ⟶ P₁) (β₂ : X₂ ⟶ P₂) (β₃ : X₃ ⟶ P₃)
    (hm₁ : adj.homEquiv X₁ Y₁ (e₁.inv ≫ α₁) = β₁ ≫ p₁)
    (hm₂ : adj.homEquiv X₂ Y₂ (e₂.inv ≫ α₂) = β₂ ≫ p₂)
    (hm₃ : adj.homEquiv X₃ Y₃ (e₃.inv ≫ α₃) = β₃ ≫ p₃.hom) :
    aI ≫ α₃ = prod.map α₁ α₂ ≫ b ↔
      a ≫ β₃ = prod.map β₁ β₂ ≫ bP := by
  have hl : aI ≫ α₃ = prod.map α₁ α₂ ≫ b ↔
      L.map a ≫ (e₃.inv ≫ α₃) =
        prodComparison L X₁ X₂ ≫
          prod.map (e₁.inv ≫ α₁) (e₂.inv ≫ α₂) ≫ b := by
    rw [hL]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← prod.map_map_assoc]
    simp only [cancel_epi]
  rw [hl, binary_mate_iff adj, hm₁, hm₂, hm₃]
  rw [← prod.map_map_assoc, ← hV]
  simp only [← Category.assoc, cancel_mono]

private noncomputable def mateIsoEquiv
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    {X P : C₀} {I Y : D₀} (e : I ≅ L.obj X) (p : P ≅ V.obj Y) :
    (I ⟶ Y) ≃ (X ⟶ P) where
  toFun α := adj.homEquiv X Y (e.inv ≫ α) ≫ p.inv
  invFun β := e.hom ≫ (adj.homEquiv X Y).symm (β ≫ p.hom)
  left_inv α := by simp [Category.assoc]
  right_inv β := by simp [Category.assoc]

private theorem mateIsoEquiv_equation
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    {X P : C₀} {I Y : D₀} (e : I ≅ L.obj X) (p : P ≅ V.obj Y)
    (α : I ⟶ Y) :
    adj.homEquiv X Y (e.inv ≫ α) = mateIsoEquiv adj e p α ≫ p.hom := by
  simp [mateIsoEquiv, Category.assoc]

private noncomputable def restrictHomEquiv
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) :
    (X₁ ⟶ X₂) ≃ (Y₁ ⟶ Y₂) where
  toFun f := Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩)
  invFun g := Classical.choose ((h (E.symm (G.map g))).mpr
    ⟨g, (E.apply_symm_apply _).symm⟩)
  left_inv f := by
    apply F.map_injective
    have hf := Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)
    have hg := Classical.choose_spec ((h (E.symm (G.map
      (Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩))))).mpr
        ⟨_, (E.apply_symm_apply _).symm⟩)
    rw [hg, hf, E.symm_apply_apply]
  right_inv g := by
    apply G.map_injective
    have hg := Classical.choose_spec ((h (E.symm (G.map g))).mpr
      ⟨g, (E.apply_symm_apply _).symm⟩)
    have hf := Classical.choose_spec ((h (F.map (Classical.choose
      ((h (E.symm (G.map g))).mpr ⟨g, (E.apply_symm_apply _).symm⟩)))).mp ⟨_, rfl⟩)
    rw [hf, hg, E.apply_symm_apply]

private theorem restrictHomEquiv_map
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) (f : X₁ ⟶ X₂) :
    G.map (restrictHomEquiv F G E h f) = E (F.map f) :=
  Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)

end Helpers

set_option maxHeartbeats 800000 in
-- The statement records every operation and its underlying comparison.

end SheafOfModules
