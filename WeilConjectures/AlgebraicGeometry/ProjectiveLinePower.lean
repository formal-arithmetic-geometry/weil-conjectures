/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Recursive fibre powers of the projective line

Source: Stacks Project, Tag 0A4F, last paragraph, and the recursive convention in
lem-weil-pbc-reduction-projective-space (blueprint: def-weil-pbc-projective-line-power).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- The `n`-fold fibre power of `P¹_T`, bundled with its projection to `T`.
Source: Stacks Project, Tag 0A4F, last paragraph; the recursion is the convention of
lem-weil-pbc-reduction-projective-space (blueprint: def-weil-pbc-projective-line-power).
At zero this is `T` with its identity; at a successor take the pullback of the previous
projection and `P¹_T → T`, with projection `pr₁ ≫ pₙ`. -/
noncomputable def projectiveLinePower (T : Scheme.{u}) : ℕ → Over T :=
  Nat.rec (Over.mk (𝟙 T)) (fun _ P ↦
    Over.mk (pullback.fst P.hom (ProjectiveLine T ↘ T) ≫ P.hom))

end AlgebraicGeometry.ProjectiveSpace
