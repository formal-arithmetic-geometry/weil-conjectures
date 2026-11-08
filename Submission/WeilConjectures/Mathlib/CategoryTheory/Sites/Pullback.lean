/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.Pullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Pullback

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.Pullback`), together
with a description of the vanishing of sections of the left Kan extension along the opposite of
a representably flat functor, which computes the sheaf pullback before sheafification
(`CategoryTheory.Functor.exists_map_eq_of_leftKanExtensionUnit_eq`).
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]

@[simp]
lemma Functor.sheafPushforwardContinuous_map_hom {G G' : Sheaf K A} (f : G ⟶ G') :
    ((F.sheafPushforwardContinuous A J K).map f).hom = F.op.whiskerLeft f.hom :=
  rfl

variable [HasWeakSheafify K A] [∀ (G : Cᵒᵖ ⥤ A), F.op.HasLeftKanExtension G]

-- TODO: move
lemma sheafToPresheaf_map {F G : Sheaf J A} (f : F ⟶ G) :
    (sheafToPresheaf _ _).map f = f.hom := by
  simp

end CategoryTheory

namespace CategoryTheory.Functor

open Limits Opposite

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  {FH : H → H → Type*} {CH : H → Type*} [∀ X Y, FunLike (FH X Y) (CH X) (CH Y)]
  [ConcreteCategory H FH]

/-- Two sections over `X` of a presheaf `P` with the same image in the pointwise left Kan
extension of `P` along the opposite of a representably flat functor `F`, at `Y` and along
`ψ : Y ⟶ F.obj X`, already agree after restriction along some `f : X' ⟶ X` through which `ψ`
factors: the left Kan extension at `Y` is a colimit over the costructured arrows, which form a
filtered category. -/
lemma exists_map_eq_of_leftKanExtensionUnit_eq (F : C ⥤ D) [RepresentablyFlat F]
    (P : Cᵒᵖ ⥤ H) [F.op.HasPointwiseLeftKanExtension P]
    [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) (forget H)]
    {X : C} {Y : D} (ψ : Y ⟶ F.obj X) (x y : ToType (P.obj (op X)))
    (h : (F.op.leftKanExtension P).map ψ.op ((F.op.leftKanExtensionUnit P).app (op X) x) =
      (F.op.leftKanExtension P).map ψ.op ((F.op.leftKanExtensionUnit P).app (op X) y)) :
    ∃ (X' : C) (f : X' ⟶ X) (ψ' : Y ⟶ F.obj X'), ψ' ≫ F.map f = ψ ∧
      P.map f.op x = P.map f.op y := by
  have : IsFiltered (CostructuredArrow F.op (op Y)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F Y)
  let hc := F.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op Y)
  let j : CostructuredArrow F.op (op Y) := CostructuredArrow.mk ψ.op
  have h' : ((LeftExtension.mk _ (F.op.leftKanExtensionUnit P)).coconeAt (op Y)).ι.app j x =
      ((LeftExtension.mk _ (F.op.leftKanExtensionUnit P)).coconeAt (op Y)).ι.app j y := by
    rw [LeftExtension.coconeAt_ι_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact h
  obtain ⟨k, g₁, g₂, hg⟩ := Concrete.isColimit_exists_of_rep_eq _ hc (i := j) (j := j) x y h'
  let g := g₁ ≫ IsFiltered.coeqHom g₁ g₂
  have hg' : P.map g.left x = P.map g.left y := by
    have e₁ : P.map g.left x = P.map (IsFiltered.coeqHom g₁ g₂).left (P.map g₁.left x) := by
      simp [g]
    have e₂ : P.map g.left y = P.map (IsFiltered.coeqHom g₁ g₂).left (P.map g₂.left y) := by
      simp only [g]
      rw [IsFiltered.coeq_condition]
      simp
    rw [e₁, e₂]
    exact congrArg _ hg
  refine ⟨_, g.left.unop, (IsFiltered.coeq g₁ g₂).hom.unop, Quiver.Hom.op_inj
    (CostructuredArrow.w g), hg'⟩

end CategoryTheory.Functor
