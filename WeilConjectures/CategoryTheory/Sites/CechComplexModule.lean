/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Čech complexes of injective presheaves of modules

Let `P` be an injective presheaf of `R`-modules. We show that the Čech complexes of the
underlying presheaf of abelian groups of `P` are exact in positive degrees: `P` is a direct
summand of the cofree presheaf of modules `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)`, whose underlying presheaf
of abelian groups is the cofree presheaf `CategoryTheory.Presheaf.cofree` of the underlying
presheaf of abelian groups of `P`, with exact Čech complexes.

## Main definitions

- `CategoryTheory.Presheaf.moduleCofree`: the cofree presheaf of modules.

## Main statements

- `CategoryTheory.Presheaf.exactAt_cechComplex_of_retraction`: the Čech complexes of a direct
  summand of the cofree presheaf are exact in positive degrees.
- `CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`: the Čech complexes of the
  underlying presheaf of abelian groups of an injective presheaf of modules are exact in
  positive degrees.
-/

@[expose] public section

universe t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C]

section Retraction

variable {V : C} [HasFiniteProducts (Over V)] {ι : Type t} (U : ι → Over V)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The Čech complex of a presheaf of abelian groups which is a direct summand of its cofree
presheaf (via `CategoryTheory.Presheaf.toCofree`) is exact in positive degrees. -/
theorem exactAt_cechComplex_of_retraction (ρ : cofree P ⟶ P) (hρ : toCofree P ≫ ρ = 𝟙 P)
    (q : ℕ) : ((cechComplex U).obj P).ExactAt (q + 1) := by
  set ι' := (cechComplex U).map (toCofree P)
  set ρ' := (cechComplex U).map ρ
  have hιρ (k : ℕ) (c : ((cechComplex U).obj P).X k) : ρ'.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hρ,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 (exactAt_cechComplex_cofree U P q)
    (ι'.f (q + 1) c) (by
      exact (ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ'.f q b, (ConcreteCategory.congr_hom (ρ'.comm q (q + 1)) b).trans
    ((congrArg (ρ'.f (q + 1)) hb).trans (hιρ _ c))⟩

end Retraction

section Module

variable {R : Type*} [Ring R] (P : Cᵒᵖ ⥤ ModuleCat.{max w v} R)

/-- The presheaf of `R`-modules `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` of families of sections of `P`
indexed by all the morphisms into `Y`, with restriction by precomposition. -/
@[simps]
noncomputable def moduleCofree : Cᵒᵖ ⥤ ModuleCat.{max w v} R where
  obj Y := ModuleCat.of R (∀ (Z : C) (_ : Z ⟶ Y.unop), P.obj (op Z))
  map {Y Y'} h := ModuleCat.ofHom
    { toFun c Z g := c Z (g ≫ h.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by
    ext c Z g
    simp
  map_comp _ _ := by
    ext c Z g
    simp

/-- The embedding of a presheaf of modules into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
@[simps]
noncomputable def toModuleCofree : P ⟶ moduleCofree P where
  app Y := ModuleCat.ofHom
    { toFun p Z g := P.map g.op p
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _
      map_smul' _ _ := funext fun _ ↦ funext fun _ ↦ map_smul _ _ _ }
  naturality Y Y' h := by
    ext p
    funext Z g
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (toModuleCofree P) := by
  have (Y : Cᵒᵖ) : Mono ((toModuleCofree P).app Y) :=
    (ModuleCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _

variable {V : C} [HasFiniteProducts (Over V)] {ι : Type t} (U : ι → Over V)

/-- The Čech complexes of the underlying presheaf of abelian groups of an injective presheaf of
modules are exact in positive degrees. -/
theorem exactAt_cechComplex_forget₂_of_injective [Injective P] (q : ℕ) :
    ((cechComplex U).obj (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})).ExactAt
      (q + 1) := by
  let r := Injective.factorThru (𝟙 P) (toModuleCofree P)
  have hr : toModuleCofree P ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let ρ : cofree (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v}) ⟶
      P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v} :=
    { app Y := AddCommGrpCat.ofHom (r.app Y).hom.toAddMonoidHom
      naturality Y Y' h := by
        ext c
        exact ConcreteCategory.congr_hom (r.naturality h) c }
  refine exactAt_cechComplex_of_retraction U _ ρ ?_ q
  ext Y p
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hr Y) p

end Module

end CategoryTheory.Presheaf
