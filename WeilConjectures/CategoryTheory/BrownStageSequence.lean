/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Algebra.Category.Grp.Limits

/-! The coproduct and kernel-killing stages in the Brown construction.

Source: Stacks Project, Derived Categories, Tag 0A8F, proof of Lemma `lemma-brown`.
(blueprint: lem-pc-brown-stage-sequence).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite
open CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{v} C]

private def elementTransformation
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] (Z : C) (x : H.obj (Opposite.op Z)) :
    preadditiveYoneda.obj Z ⟶ H where
  app K := AddCommGrpCat.ofHom
    { toFun := fun f ↦ H.map f.op x
      map_zero' := by simp
      map_add' := by
        intro f g
        exact congrArg (fun t : H.obj (Opposite.op Z) ⟶ H.obj K ↦ t x)
          (H.map_add (f := f.op) (g := g.op)) }
  naturality := by
    intro K L f
    ext g
    change H.map (f.unop ≫ g).op x = H.map f (H.map g.op x)
    rw [op_comp, H.map_comp]
    rfl

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasCoproducts.{v} C] in
private theorem stage_elementTransformation_value
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] (Z : C)
    (β : preadditiveYoneda.obj Z ⟶ H) (K : C) (f : K ⟶ Z) :
    H.map f.op (β.app (Opposite.op Z) (𝟙 Z)) = β.app (Opposite.op K) f := by
  have h := ConcreteCategory.congr_hom (β.naturality f.op) (𝟙 Z)
  change β.app (Opposite.op K) (f ≫ 𝟙 Z) =
    H.map f.op (β.app (Opposite.op Z) (𝟙 Z)) at h
  rw [Category.comp_id] at h
  exact h.symm

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem stage_coproduct_element
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    {J : Type v} (A : J → C) (a : ∀ j, H.obj (Opposite.op (A j))) :
    ∃ x : H.obj (Opposite.op (∐ A)), ∀ j, H.map (Sigma.ι A j).op x = a j := by
  have := hH J
  let F := H ⋙ forget AddCommGrpCat
  let c := (Cofan.mk (∐ A) (Sigma.ι A)).op
  have hc : IsLimit (F.mapCone c) :=
    isLimitOfPreserves F (Cofan.IsColimit.op (coproductIsCoproduct A))
  let s : ∀ j : Discrete J, (Discrete.functor (fun j ↦ Opposite.op (A j)) ⋙ F).obj j :=
    fun j ↦ a j.as
  have hs : s ∈ (Discrete.functor (fun j ↦ Opposite.op (A j)) ⋙ F).sections := by
    intro j k f
    obtain ⟨j⟩ := j
    obtain ⟨k⟩ := k
    obtain rfl := Discrete.eq_of_hom f
    simp
  obtain ⟨x, hx, _⟩ := (Types.isLimit_iff _).1 ⟨hc⟩ s hs
  exact ⟨x, fun j ↦ hx ⟨j⟩⟩

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem stage_coproduct_element_zero
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    {J : Type v} (A : J → C) (x : H.obj (Opposite.op (∐ A)))
    (hx : ∀ j, H.map (Sigma.ι A j).op x = 0) : x = 0 := by
  have := hH J
  let F := H ⋙ forget AddCommGrpCat
  let c := (Cofan.mk (∐ A) (Sigma.ι A)).op
  have hc : IsLimit (F.mapCone c) :=
    isLimitOfPreserves F (Cofan.IsColimit.op (coproductIsCoproduct A))
  apply (Types.isLimitEquivSections hc).injective
  apply Subtype.ext
  funext j
  change H.map (Sigma.ι A j.as).op x = H.map (Sigma.ι A j.as).op 0
  rw [hx, map_zero]

private theorem initial_stage {J : Type v} (A : J → C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ (Z : C) (β : preadditiveYoneda.obj Z ⟶ H),
      ∀ j, Function.Surjective (β.app (Opposite.op (A j))) := by
  let T := Σ j : J, H.obj (Opposite.op (A j))
  let B : T → C := fun t ↦ A t.1
  obtain ⟨x, hx⟩ := stage_coproduct_element H hH B (fun t ↦ t.2)
  refine ⟨∐ B, elementTransformation H (∐ B) x, ?_⟩
  intro j a
  exact ⟨Sigma.ι B ⟨j, a⟩, hx ⟨j, a⟩⟩

private theorem next_stage {J : Type v} (A : J → C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H)
    (Z : C) (β : preadditiveYoneda.obj Z ⟶ H) :
    ∃ (W : C) (t : Z ⟶ W) (γ : preadditiveYoneda.obj W ⟶ H),
      preadditiveYoneda.map t ≫ γ = β ∧
      ∀ (j : J) (f : A j ⟶ Z), β.app (Opposite.op (A j)) f = 0 → f ≫ t = 0 := by
  let T := Σ j : J, {f : A j ⟶ Z // β.app (Opposite.op (A j)) f = 0}
  let B : T → C := fun k ↦ A k.1
  let k : (∐ B) ⟶ Z := Sigma.desc (fun a : T ↦ a.2.1)
  let x := β.app (Opposite.op Z) (𝟙 Z)
  have hk : H.map k.op x = 0 := by
    refine stage_coproduct_element_zero H hH B (H.map k.op x) ?_
    intro a
    rw [← AddCommGrpCat.comp_apply, ← H.map_comp, ← op_comp]
    change H.map (Sigma.ι B a ≫ Sigma.desc (fun a : T ↦ a.2.1)).op x = 0
    rw [Sigma.ι_desc]
    exact (stage_elementTransformation_value H Z β (A a.1) a.2.1).trans a.2.2
  obtain ⟨W, t, r, htri⟩ := Pretriangulated.distinguished_cocone_triangle k
  have hex := H.map_distinguished_op_exact (Triangle.mk k t r) htri
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1 hex x hk
  change H.map t.op y = x at hy
  refine ⟨W, t, elementTransformation H W y, ?_, ?_⟩
  · ext K f
    change H.map (f ≫ t).op y = β.app K f
    rw [op_comp, H.map_comp, AddCommGrpCat.comp_apply, hy]
    exact stage_elementTransformation_value H Z β K.unop f
  · intro j f hf
    have ht := Pretriangulated.comp_distTriang_mor_zero₁₂ (Triangle.mk k t r) htri
    change k ≫ t = 0 at ht
    have hi := congrArg (fun z : (∐ B) ⟶ W ↦ Sigma.ι B ⟨j, f, hf⟩ ≫ z) ht
    simpa [k] using hi

/-- There is a compatible sequence of Yoneda transformations initially surjective on
all shifted test objects, whose transitions kill their kernels.

Source: Stacks Project, Derived Categories, Tag 0A8F, first two paragraphs of the proof
of Lemma `lemma-brown` (blueprint: lem-pc-brown-stage-sequence).

Proof: index the first coproduct by triples `(i, n, a)` with `a ∈ H(E i[n])`.
All indices fit in Type v, using a universe lift of the integer index. Product
preservation identifies H of this coproduct with the product of the summand values.
The tuple of the elements a specifies an element on the coproduct. Since H is additive,
additive Yoneda makes this element a group-valued natural transformation β₀; each
coproduct inclusion maps to its indexing element, proving initial surjectivity.
Given a stage and its transformation, take the coproduct of all maps from E i[n]
whose value under that transformation is zero. Its summand maps induce a morphism
into the stage. H of this morphism kills the stage element, since each product
projection is zero. Complete the morphism to a distinguished triangle. Exactness
of H lifts the stage element across the second triangle morphism, giving the next
transformation and compatibility. Each indexed kernel map composes to zero by the
consecutive-composition identity for a distinguished triangle. Dependent choice
constructs the natural-number sequence, and the functor from the natural-number
preorder is defined by finite composites of these successive transition maps.
Compactness and generation are not needed for any of these steps. -/
theorem brownStageSequence {I : Type v} (E : I → C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (J : Type v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ (X : ℕ ⥤ C) (β : ∀ j : ℕ, preadditiveYoneda.obj (X.obj j) ⟶ H),
      (∀ j : ℕ,
        preadditiveYoneda.map (X.map (homOfLE (Nat.le_succ j))) ≫ β (j + 1) = β j) ∧
      (∀ (i : I) (n : ℤ), Function.Surjective (β 0 |>.app (Opposite.op ((E i)⟦n⟧)))) ∧
      (∀ (j : ℕ) (i : I) (n : ℤ) (f : (E i)⟦n⟧ ⟶ X.obj j),
        (β j).app (Opposite.op ((E i)⟦n⟧)) f = 0 →
          f ≫ X.map (homOfLE (Nat.le_succ j)) = 0) := by
  classical
  let A : I × ULift.{v} ℤ → C := fun j ↦ (E j.1)⟦j.2.down⟧
  obtain ⟨Z, β, hsurj⟩ := initial_stage A H hH
  choose W t γ hγ hkill using fun (Z : C) (β : preadditiveYoneda.obj Z ⟶ H) ↦
    next_stage A H hH Z β
  let S : ℕ → Σ Z : C, preadditiveYoneda.obj Z ⟶ H :=
    Nat.rec ⟨Z, β⟩ (fun _ s ↦ ⟨W s.1 s.2, γ s.1 s.2⟩)
  let τ : ∀ j : ℕ, (S j).1 ⟶ (S (j + 1)).1 := fun j ↦ t (S j).1 (S j).2
  refine ⟨Functor.ofSequence τ, fun j ↦ (S j).2, ?_, ?_, ?_⟩
  · intro j
    simpa only [Functor.ofSequence_map_homOfLE_succ] using hγ (S j).1 (S j).2
  · intro i n
    exact hsurj ⟨i, ⟨n⟩⟩
  · intro j i n f hf
    simpa only [Functor.ofSequence_map_homOfLE_succ] using
      hkill (S j).1 (S j).2 ⟨i, ⟨n⟩⟩ f hf

end CategoryTheory
