/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-! # Third Hom comparison for a cofiltered diagram of distinguished triangles

Source: Stacks Project, Derived Categories, Lemma 05SC, five-term Hom diagram, dualized.
(blueprint: lem-pur-triangulated-hom-colimit-comparison).
-/

@[expose] public section

universe uJ vJ uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A triangle morphism at one stage induces bijective third Hom comparisons if it
induces bijective first and second Hom comparisons for every test object.

Source: Stacks Project, Derived Categories, Lemma 05SC, displayed five-term Hom diagram,
with contravariant Hom and cofiltered indexing.
(blueprint: lem-pur-triangulated-hom-colimit-comparison).

Proof: For a test object W apply Hom(-,W) to the distinguished triangles H(j) and U.
The five terms are Hom(second[1],W), Hom(first[1],W), Hom(third,W), Hom(second,W),
and Hom(first,W). Triangle morphisms give a diagram of exact sequences over J opposite.
Its filtered colimit is exact (filtered colimits of abelian groups preserve exactness).
Precomposition with m gives a map from the exact sequence of U to this colimit sequence;
the triangle-morphism equations ensure all four squares commute. The last two vertical
maps are bijective by h₂ and h₁. The first two are bijective by the same hypotheses with
W shifted by -1, using the shift equivalence and its natural Hom bijections. The five
lemma makes the middle vertical map bijective. Forgetting the abelian group structures
identifies the filtered colimit with ColimitType, and its middle vertical map sends phi
to the class of m.hom₃ followed by phi at j₀, exactly the map below. -/
theorem triangulated_hom_colimit_comparison
    {J : Type uJ} {D : Type uD} [Category.{vJ} J] [Category.{vD} D]
    [IsCofiltered J] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (H : J ⥤ Triangle D) (hH : ∀ j, H.obj j ∈ distTriang D)
    (U : Triangle D) (hU : U ∈ distTriang D) (j₀ : J) (m : H.obj j₀ ⟶ U)
    (h₁ : ∀ W : D, Function.Bijective (fun φ : U.obj₁ ⟶ W ↦
      (((H ⋙ Triangle.π₁).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₁ ≫ φ))))
    (h₂ : ∀ W : D, Function.Bijective (fun φ : U.obj₂ ⟶ W ↦
      (((H ⋙ Triangle.π₂).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₂ ≫ φ)))) :
    ∀ W : D, Function.Bijective (fun φ : U.obj₃ ⟶ W ↦
      (((H ⋙ Triangle.π₃).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₃ ≫ φ))) := by sorry

end CategoryTheory
