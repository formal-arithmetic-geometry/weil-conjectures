/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Pullback of free sheaves on representables

Let `G : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, and let
`L : Sheaf J A ⥤ Sheaf K A` be a left adjoint of the pushforward
`G.sheafPushforwardContinuous A J K`. Then `L` sends the free sheaf `Sheaf.freeYoneda J X M`
on `X : C` with coefficients `M : A` to the free sheaf `Sheaf.freeYoneda K (G.obj X) M`
(`CategoryTheory.Sheaf.freeYonedaPullbackIso`): both corepresent `F ↦ (M ⟶ F(G X))`.

-/

@[expose] public section

universe w v v₂ v' u u₂ u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasCoproducts.{v} A] [HasWeakSheafify J A]

/-- `Sheaf.freeYonedaHomEquiv` is natural in the target. -/
lemma freeYonedaHomEquiv_comp {X : C} {M : A} {F F' : Sheaf J A}
    (α : freeYoneda J X M ⟶ F) (f : F ⟶ F') :
    freeYonedaHomEquiv (α ≫ f) = freeYonedaHomEquiv α ≫ f.hom.app (op X) := by
  simp only [freeYonedaHomEquiv, Equiv.trans_apply]
  have h := (sheafificationAdjunction J A).homEquiv_naturality_right
    (X := Presheaf.freeYoneda X M) α f
  erw [h, Presheaf.freeYonedaHomEquiv_comp]
  rfl

/-- `(Sheaf.freeYonedaHomEquiv).symm` is natural in the target. -/
lemma freeYonedaHomEquiv_symm_comp {X : C} {M : A} {F F' : Sheaf J A}
    (a : M ⟶ F.obj.obj (op X)) (f : F ⟶ F') :
    freeYonedaHomEquiv.symm a ≫ f = freeYonedaHomEquiv.symm (a ≫ f.hom.app (op X)) := by
  apply freeYonedaHomEquiv.injective
  rw [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) {K : GrothendieckTopology D}
  [HasCoproducts.{v₂} A] [HasWeakSheafify K A] [G.IsContinuous J K]
  {L : Sheaf J A ⥤ Sheaf K A} (adj : L ⊣ G.sheafPushforwardContinuous A J K)

/-- The natural bijection `(freeYoneda K (G.obj X) M ⟶ F) ≃ (L.obj (freeYoneda J X M) ⟶ F)`. -/
noncomputable def freeYonedaPullbackHomEquiv (X : C) (M : A) (F : Sheaf K A) :
    (freeYoneda K (G.obj X) M ⟶ F) ≃ (L.obj (freeYoneda J X M) ⟶ F) :=
  freeYonedaHomEquiv.trans
    ((freeYonedaHomEquiv (F := (G.sheafPushforwardContinuous A J K).obj F)).symm.trans
      (adj.homEquiv _ _).symm)

lemma freeYonedaPullbackHomEquiv_comp {X : C} {M : A} {F F' : Sheaf K A}
    (a : freeYoneda K (G.obj X) M ⟶ F) (φ : F ⟶ F') :
    freeYonedaPullbackHomEquiv G adj X M F' (a ≫ φ) =
      freeYonedaPullbackHomEquiv G adj X M F a ≫ φ := by
  simp only [freeYonedaPullbackHomEquiv, Equiv.trans_apply]
  rw [freeYonedaHomEquiv_comp, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  exact (freeYonedaHomEquiv_symm_comp (F := (G.sheafPushforwardContinuous A J K).obj F)
    (F' := (G.sheafPushforwardContinuous A J K).obj F') (freeYonedaHomEquiv (J := K) a)
    ((G.sheafPushforwardContinuous A J K).map φ)).symm

/-- The left adjoint of the pushforward along a continuous functor `G` sends the free sheaf on
`X` to the free sheaf on `G.obj X`. -/
noncomputable def freeYonedaPullbackIso (X : C) (M : A) :
    L.obj (freeYoneda J X M) ≅ freeYoneda K (G.obj X) M :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun F ↦ Equiv.toIso (freeYonedaPullbackHomEquiv G adj X M F)) (by
      intro F F' φ
      ext a
      exact freeYonedaPullbackHomEquiv_comp G adj a φ))).unop

end CategoryTheory.Sheaf
