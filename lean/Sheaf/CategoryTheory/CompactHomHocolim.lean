/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.CategoryTheory.CompactObject
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Compact Hom commutes with sequential homotopy colimits

Source: Stacks Project, Derived Categories, Lemma 13.33.9 (Tag 094A)
(blueprint: lem-pc-compact-hom-hocolim).
-/

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/-- For compact `K`, the canonical comparison from the sequential colimit of `Hom(K, X n)`
to `Hom(K, Y)` is bijective when `Y` belongs to the telescope triangle.
Source: Stacks Project, Derived Categories, Tag 094A
(blueprint: lem-pc-compact-hom-hocolim).

The equations on the stage maps specify the canonical comparison uniquely by the colimit
universal property. The coproduct index is lifted to the universe of compactness.

Proof: put `A = ⨁ X n`. Compactness (`def-pc-compact-object`) identifies `Hom(K, A)`
and `Hom(K, A[1])` with the sums of `Hom(K, X n)` and `Hom(K, X n[1])`.
The endomorphism induced by identity minus shift becomes identity minus the transition
shift on these sums. It is injective: its zeroth component forces the zeroth input to vanish,
and induction forces every later component to vanish. Apply triangle exactness
(`lem-weil-pbc-hom-into-triangle-exact`) and the vanishing of consecutive compositions to
the telescope triangle and its rotation. Every map `K → Y` then factors through `q`, and
the kernel of postcomposition with `q` is the image of identity minus shift.
Finally, the cokernel of identity minus shift on the sum of the Hom groups is their
sequential direct limit: its relations identify an element at stage `n` with its image at
stage `n + 1`. The resulting bijection has the displayed values on all stage inclusions. -/
theorem compact_hom_hocolim
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    (K : C) (hK : IsCompactObject K) (X : ℕ ⥤ C) (Y : C)
    (q : (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down) ⟶ Y)
    (r : Y ⟶ (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 (∐ fun n : ULift.{w} ℕ ↦ X.obj n.down) -
        Sigma.desc (fun n : ULift.{w} ℕ ↦
          X.map (homOfLE (Nat.le_succ n.down)) ≫
            Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n.down + 1⟩))
      q r ∈ distTriang C) :
    ∃ φ : colimit (X ⋙ coyoneda.obj (op K)) → (K ⟶ Y),
      (∀ (n : ℕ) (f : K ⟶ X.obj n),
        φ (colimit.ι (X ⋙ coyoneda.obj (op K)) n f) =
          f ≫ Sigma.ι (fun k : ULift.{w} ℕ ↦ X.obj k.down) ⟨n⟩ ≫ q) ∧
      Function.Bijective φ := by
  sorry

end CategoryTheory
