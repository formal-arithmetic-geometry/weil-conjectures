/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.Triangulated.RoosSpecialTriangleIso

/-!
# Cancellation of a finite split summand in a distinguished triangle

Source: Stacks Project, derived.tex, Tag 05QS, Lemma 13.4.7, lines 639--650
(blueprint: lem-sp-roos-split-summand-cancellation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/--
For two triangles in a pre-triangulated category, the componentwise binary direct-sum
triangle is distinguished exactly when both summand triangles are distinguished.
Source: Stacks Project, derived.tex, Tag 05QS, Lemma 13.4.7, lines 639--650
(blueprint: lem-sp-roos-split-summand-cancellation).

Proof (node lem-sp-roos-split-summand-cancellation).
1. Write T, T' for the two triangles and D for the displayed direct-sum triangle. Use the
   three clauses of lem-sp-roos-special-triangle-iso: distinguished triangles are
   co-special; D is co-special iff T and T' are; a morphism from a co-special triangle
   to a distinguished one with invertible first two components makes its source
   distinguished (def-weil-triangulated-category).
2. If D is distinguished, T and T' are co-special. TR1 gives a distinguished cone
   triangle with first arrow f; TR3 extends the biproduct projections on the first two
   vertices to a morphism p from D to it. With the inclusion morphism i : T ⟶ D, the
   composite i ≫ p has identity first two components, so T is distinguished.
   The same with inr and snd gives T'.
3. If T and T' are distinguished, D is co-special. TR1 gives a distinguished cone
   triangle with first arrow f ⊕ f'; TR3 extends the inclusions to morphisms a, b from
   T, T' into it. The morphism from D with components 𝟙, 𝟙 and biprod.desc a.hom₃ b.hom₃
   (squares checked on inl and inr) makes D distinguished by the criterion.
-/
theorem roos_split_summand_cancellation
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y Z X' Y' Z' : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (h' : Z' ⟶ X'⟦(1 : ℤ)⟧) :
    (Triangle.mk (biprod.map f f') (biprod.map g g')
        (biprod.desc (h ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
          (h' ≫ (shiftFunctor C (1 : ℤ)).map biprod.inr))
        ∈ distTriang C) ↔
      (Triangle.mk f g h ∈ distTriang C ∧ Triangle.mk f' g' h' ∈ distTriang C) := by
  let T := Triangle.mk f g h
  let T' := Triangle.mk f' g' h'
  let D := directSumTriangle T T'
  change D ∈ distTriang C ↔ T ∈ distTriang C ∧ T' ∈ distTriang C
  obtain ⟨coSpecial, sumCoSpecial, criterion⟩ := roos_special_triangle_iso (C := C)
  constructor
  · intro hD
    obtain ⟨hT, hT'⟩ := (sumCoSpecial T T').mp (coSpecial D hD)
    let i : T ⟶ D :=
      { hom₁ := biprod.inl
        hom₂ := biprod.inl
        hom₃ := biprod.inl
        comm₁ := by simp [T, D, directSumTriangle]
        comm₂ := by simp [T, D, directSumTriangle]
        comm₃ := by simp [T, D, directSumTriangle] }
    let i' : T' ⟶ D :=
      { hom₁ := biprod.inr
        hom₂ := biprod.inr
        hom₃ := biprod.inr
        comm₁ := by simp [T', D, directSumTriangle]
        comm₂ := by simp [T', D, directSumTriangle]
        comm₃ := by simp [T', D, directSumTriangle] }
    constructor
    · obtain ⟨Q, q, r, hQ⟩ := distinguished_cocone_triangle f
      let p : D ⟶ Triangle.mk f q r :=
        completeDistinguishedTriangleMorphism _ _ hD hQ biprod.fst biprod.fst
          (by
            change biprod.map f f' ≫ biprod.fst = biprod.fst ≫ f
            exact biprod.map_fst f f')
      apply criterion hT hQ (i ≫ p)
      · change IsIso (biprod.inl ≫ biprod.fst : X ⟶ X)
        simp only [biprod.inl_fst]
        infer_instance
      · change IsIso (biprod.inl ≫ biprod.fst : Y ⟶ Y)
        simp only [biprod.inl_fst]
        infer_instance
    · obtain ⟨Q, q, r, hQ⟩ := distinguished_cocone_triangle f'
      let p : D ⟶ Triangle.mk f' q r :=
        completeDistinguishedTriangleMorphism _ _ hD hQ biprod.snd biprod.snd
          (by
            change biprod.map f f' ≫ biprod.snd = biprod.snd ≫ f'
            exact biprod.map_snd f f')
      apply criterion hT' hQ (i' ≫ p)
      · change IsIso (biprod.inr ≫ biprod.snd : X' ⟶ X')
        simp only [biprod.inr_snd]
        infer_instance
      · change IsIso (biprod.inr ≫ biprod.snd : Y' ⟶ Y')
        simp only [biprod.inr_snd]
        infer_instance
  · rintro ⟨hT, hT'⟩
    have hD := (sumCoSpecial T T').mpr ⟨coSpecial T hT, coSpecial T' hT'⟩
    obtain ⟨Q, q, r, hQ⟩ := distinguished_cocone_triangle (biprod.map f f')
    let a : T ⟶ Triangle.mk (biprod.map f f') q r :=
      completeDistinguishedTriangleMorphism _ _ hT hQ biprod.inl biprod.inl
        (by
          change f ≫ biprod.inl = biprod.inl ≫ biprod.map f f'
          exact (biprod.inl_map f f').symm)
    let b : T' ⟶ Triangle.mk (biprod.map f f') q r :=
      completeDistinguishedTriangleMorphism _ _ hT' hQ biprod.inr biprod.inr
        (by
          change f' ≫ biprod.inr = biprod.inr ≫ biprod.map f f'
          exact (biprod.inr_map f f').symm)
    let c : D ⟶ Triangle.mk (biprod.map f f') q r :=
      { hom₁ := 𝟙 _
        hom₂ := 𝟙 _
        hom₃ := biprod.desc a.hom₃ b.hom₃
        comm₁ := by
          change biprod.map f f' ≫ 𝟙 _ = 𝟙 _ ≫ biprod.map f f'
          simp only [Category.comp_id, Category.id_comp]
        comm₂ := by
          apply biprod.hom_ext' <;>
            simpa [D, directSumTriangle, T, T', Category.assoc] using
              (by first | exact a.comm₂ | exact b.comm₂)
        comm₃ := by
          apply biprod.hom_ext' <;>
            simpa [D, directSumTriangle, T, T', Category.assoc] using
              (by first | exact a.comm₃ | exact b.comm₃) }
    apply criterion hD hQ c <;> change IsIso (𝟙 _) <;> infer_instance

end CategoryTheory
