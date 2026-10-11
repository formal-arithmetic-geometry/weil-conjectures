/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem

/-! # Common refinements of denominator triangles

Source: Stacks Project, Derived Categories, Tag 05R9, with arrows reversed
(blueprint: lem-pur-triangle-common-refinement-ms3-05r9).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Finite families of distinguished denominator triangles over `T` have a common predecessor,
and parallel denominator triangle morphisms are equalized by another denominator triangle.
Source: Stacks Project, Derived Categories, Tag 05R9, dual construction
(blueprint: lem-pur-triangle-common-refinement-ms3-05r9).

Proof: (1) The right fraction calculus makes `S/X` cofiltered. Saturation ensures every
commuting arrow between denominators lies in `S`: use MS2 to complete a square, MS3 to
cancel its denominator, and MS4 on the two resulting composites. For two triangles choose
an X-predecessor and complete its S-map to a distinguished denominator triangle by
`lem-pur-triangle-completion-ms6-05r9`. Rotate and repeat for Y and Z. The candidate component
maps agree with the fixed maps into T. MS3 gives a further S-precomposition making the
first triangle square commute; complete this map to a denominator triangle. Rotate and
repeat for the remaining squares. Earlier equalities persist under precomposition and MS1
keeps all components in S. Iterate for a finite nonempty family; for the empty family use
the identity of T.
(2) For parallel maps, their composites with the target denominator agree. MS3 gives an
S-map into the common source equalizing their first components. Complete it to a
triangle map by `lem-pur-triangle-completion-ms6-05r9`. Rotate and repeat for the second and
third components. Precomposition preserves earlier equalities and MS1 preserves membership
in S. The final composite is the required equalizer arrow.
(3) All chosen triangles are distinguished, all component maps lie in S, and all maps
commute over T. Thus these are precisely the finite-predecessor and parallel-equalization
conditions of the category in the node. -/
theorem triangle_common_refinement_and_equalization
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C) :
    (∀ (I : Type w) [Finite I] (D : I → Triangle C) (s : ∀ i : I, D i ⟶ T),
      (∀ i : I, D i ∈ distTriang C) →
      (∀ i : I, S (s i).hom₁ ∧ S (s i).hom₂ ∧ S (s i).hom₃) →
      ∃ (U : Triangle C) (t : U ⟶ T), U ∈ distTriang C ∧
        S t.hom₁ ∧ S t.hom₂ ∧ S t.hom₃ ∧
        ∀ i : I, ∃ a : U ⟶ D i,
          S a.hom₁ ∧ S a.hom₂ ∧ S a.hom₃ ∧ a ≫ s i = t) ∧
    (∀ (D E : Triangle C) (s : D ⟶ T) (t : E ⟶ T),
      D ∈ distTriang C → E ∈ distTriang C →
      S s.hom₁ → S s.hom₂ → S s.hom₃ →
      S t.hom₁ → S t.hom₂ → S t.hom₃ →
      ∀ a b : D ⟶ E,
        S a.hom₁ → S a.hom₂ → S a.hom₃ →
        S b.hom₁ → S b.hom₂ → S b.hom₃ →
        a ≫ t = s → b ≫ t = s →
        ∃ (U : Triangle C) (r : U ⟶ T) (q : U ⟶ D), U ∈ distTriang C ∧
          S r.hom₁ ∧ S r.hom₂ ∧ S r.hom₃ ∧
          S q.hom₁ ∧ S q.hom₂ ∧ S q.hom₃ ∧ q ≫ s = r ∧
          q.hom₁ ≫ a.hom₁ = q.hom₁ ≫ b.hom₁ ∧
          q.hom₂ ≫ a.hom₂ = q.hom₂ ≫ b.hom₂ ∧
          q.hom₃ ≫ a.hom₃ = q.hom₃ ≫ b.hom₃) := by
  sorry

end CategoryTheory
