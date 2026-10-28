/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso

/-! # Target projection model transport for ordinary finite reduction

The completed pullback followed by target projection is identified with the canonical
finite quotient model. This is the geometric part of the target transport.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- The target projection model is the canonical finite quotient pullback model.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL and 093M.
Proof: use the second-site quotient identification, the projection equation for
`completedMap`, and normalized scalar associativity for inverse-image pullback.
(blueprint: lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso).
-/
theorem ordinaryReducedPull_targetProjectionIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ change (projection J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) := by
  sorry

end CategoryTheory.ConstantCompletion
