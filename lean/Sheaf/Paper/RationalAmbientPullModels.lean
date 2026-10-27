/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.RationalStratumPullbackData


/-! # Normalized ambient rational module pullback counits -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RationalStratumPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ambient pullback has the normalized universal counit and computes on K-flat complexes.
Source: Stacks 06YY; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-per-rational-ambient-pull-models).

Proof: exact module inverse image is computed termwise and preserves acyclic tensor
K-flat complexes. Compose its derived comparison with the scalar-extension counit.
Remove the identity scalar factor by multiplication, with inverse insertion of one.
Apply the same ordinary comparison termwise. Its section formula is multiplication
on every pure tensor, so the resulting counit has IsNormalizedPullCounit. The
universal property follows by composition of the exact functor with the universal
left derived scalar extension. Exact inverse image preserves K-flatness; hence the
scalar counit, and therefore this counit, is invertible on every K-flat complex.
No condition on the scheme morphism or flatness of its coefficient map is used. -/
theorem rational_ambient_pull_models {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Nonempty (Pull l E f (coefficient l E f)) := by sorry

end AlgebraicGeometry.Scheme.RationalStratumPullback
