/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# The internal hom of presheaves of modules is a sheaf

Let `R` be a presheaf of commutative rings on a site `(C, J)`. If `N` is a presheaf of modules
over `R` whose underlying presheaf of abelian groups is a sheaf, then so is the internal hom
`PresheafOfModules.homObj M N`, for every presheaf of modules `M`.

The sections of `homObj M N` over `U` are the morphisms `M|_U ⟶ N|_U`, i.e. the morphisms of
the underlying presheaves of abelian groups (sections of `presheafHom`) that are linear. The
presheaf `presheafHom` is a sheaf by `Presheaf.IsSheaf.hom`, and linearity of a glued morphism
can be checked locally because `N` is separated.

## Main results

- `PresheafOfModules.isSheaf_homObj`: `homObj M N` is a sheaf if `N` is.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- A section of `homObj M N` over `U`, i.e. a morphism between restrictions of presheaves of
modules to `Over U`, gives a section of `presheafHom M.presheaf N.presheaf` over `U` by taking
the underlying morphism of presheaves of abelian groups. -/
noncomputable def homObjToPresheafHom (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) :
    (homObj M N).presheaf ⋙ forget AddCommGrpCat ⟶ presheafHom M.presheaf N.presheaf where
  app X := ↾fun φ ↦ (toPresheaf _).map φ
  naturality X Y g := by
    ext φ
    rfl

/-- `homObjToPresheafHom` is injective on sections: a morphism of presheaves of modules is
determined by its underlying morphism of presheaves of abelian groups. -/
lemma homObjToPresheafHom_injective (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    Function.Injective ((homObjToPresheafHom M N).app X) :=
  fun _ _ h ↦ (toPresheaf _).map_injective h

/-- The internal hom `homObj M N` of presheaves of modules is a sheaf if `N` is. -/
lemma isSheaf_homObj (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
    (hN : Presheaf.IsSheaf J N.presheaf) : Presheaf.IsSheaf J (homObj M N).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget AddCommGrpCat.{max u₁ v₁ v}),
    isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  have hG : Presieve.IsSheafFor (presheafHom M.presheaf N.presheaf) S.arrows :=
    presheafHom_isSheafFor _ _ S
      (fun _ _ ↦ ((Presheaf.isSheaf_iff_isLimit J _).1 hN _ (J.pullback_stable _ hS)).some)
  have hN' : Presieve.IsSheaf J (N.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf J _ _ hN)
  obtain ⟨y', hy', -⟩ := hG _ (hx.map (homObjToPresheafHom M N))
  have hy'' := (PresheafHom.isAmalgamation_iff _ _ (hx.map _) _).1 hy'
  have key (W : (Over X)ᵒᵖ) {T : C} (p : T ⟶ W.unop.left) (hp : S (p ≫ W.unop.hom))
      (z : M.obj (op W.unop.left)) :
      N.map p.op (y'.app W z) =
        (x (p ≫ W.unop.hom) hp).app (op (Over.mk (𝟙 T))) (M.map p.op z) := by
    have h := NatTrans.naturality_apply y' (Over.homMk p : Over.mk (p ≫ W.unop.hom) ⟶ W.unop).op z
    exact h.symm.trans (ConcreteCategory.congr_hom (hy'' _ _ hp) _)
  let y : (restrictOver R X).obj M ⟶ (restrictOver R X).obj N := homMk y' fun W r m ↦ by
    refine (hN' _ (J.pullback_stable W.unop.hom hS)).isSeparatedFor.ext fun T p hp ↦ ?_
    refine (key W p hp _).trans ?_
    erw [PresheafOfModules.map_smul, PresheafOfModules.map_smul, key W p hp m]
    exact ((x _ hp).app _).hom.map_smul _ _
  have hy : (homObjToPresheafHom M N).app (op X) y = y' := rfl
  refine ⟨y, fun Y f hf ↦ homObjToPresheafHom_injective M N _ ?_,
    fun z hz ↦ homObjToPresheafHom_injective M N _ ?_⟩
  · exact (NatTrans.naturality_apply (homObjToPresheafHom M N) f.op y).trans (hy ▸ hy' f hf)
  · exact hG.isSeparatedFor _ _ _ (hz.map _) (hy ▸ hy')

end PresheafOfModules
