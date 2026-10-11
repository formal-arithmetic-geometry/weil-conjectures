/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator

/-!
# Building objects from compact generators

Source: Stacks Project, Derived Categories, Lemma 13.37.4 (Tag 09SN)
(blueprint: lem-pc-compact-generators-build-objects).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Every object is the sequential homotopy colimit of a sequence built from coproducts
of shifts of compact generators (Stacks, Tag 09SN)
(blueprint: lem-pc-compact-generators-build-objects).

For the proof, start with the coproduct of all shifted generators mapping to `Y`.
At each stage take the coproduct of all shifted generators mapping to the current
object whose composites to `Y` vanish, and complete its map to a distinguished
triangle. Exactness gives compatible maps from the successive objects to `Y`.
Their coproduct map vanishes on identity minus shift, so it factors through the
homotopy colimit. Complete that map to a triangle with cone `C`. Compactness
lets every map from a shifted generator to the telescope factor through a stage;
the next triangle kills it. Exactness then lifts any map from a shifted generator
to `C` to a shifted map into `Y`. This map occurs among the summands at the first
stage, so its image in `C` is zero. Generation forces `C` to be zero, making the
telescope map an isomorphism; transport the telescope triangle along it. -/
theorem compactGenerators_buildObjects
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{max w v} C]
    {I : Type (max w v)} (E : I → C)
    (hcompact : ∀ i : I, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E) (Y : C) :
    ∃ (X : ℕ → C) (t : ∀ n : ℕ, X n ⟶ X (n + 1)),
      (∃ (J : Type (max w v)) (i : J → I) (m : J → ℤ),
        Nonempty (X 0 ≅ ∐ fun j : J => (E (i j))⟦m j⟧)) ∧
      (∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ X n)
          (b : ∀ n : ℕ, X (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
        (∀ n : ℕ, ∃ (J : Type (max w v)) (i : J → I) (m : J → ℤ),
          Nonempty (Z n ≅ ∐ fun j : J => (E (i j))⟦m j⟧)) ∧
        ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C) ∧
      ∃ (q : (∐ fun n : ULift.{max w v} ℕ => X n.down) ⟶ Y)
          (r : Y ⟶ (∐ fun n : ULift.{max w v} ℕ => X n.down)⟦(1 : ℤ)⟧),
        Triangle.mk
          (𝟙 (∐ fun n : ULift.{max w v} ℕ => X n.down) -
            Sigma.desc (fun n : ULift.{max w v} ℕ =>
              t n.down ≫ Sigma.ι (fun k : ULift.{max w v} ℕ => X k.down)
                ⟨n.down + 1⟩))
          q r ∈ distTriang C := by
  sorry

end CategoryTheory
