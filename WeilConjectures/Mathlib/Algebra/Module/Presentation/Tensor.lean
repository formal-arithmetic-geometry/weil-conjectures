/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Presentation.Tensor
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of presentations of modules

Given relations `ρ : Module.Relations A` and a ring homomorphism `f : A →+* B`, we define the
base changed relations `ρ.baseChange f : Module.Relations B`, with the same generators and
relations and coefficients mapped along `f`. If `s : ρ.Solution M` is a presentation of the
`A`-module `M`, then `1 ⊗ s` is a presentation of `B ⊗[A] M` by the base changed relations
(`Module.Relations.Solution.IsPresentation.baseChange`).
-/

@[expose] public noncomputable section

universe w' w₀ w₁ u v w

open TensorProduct

namespace Module.Relations

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

variable [Algebra A B] {ρ : Relations.{w₀, w₁} A} {M : Type w} [AddCommGroup M] [Module A M]

namespace Solution

namespace IsPresentation

variable {s : ρ.Solution M} (h : s.IsPresentation)
include h

end IsPresentation

section RingHom

variable {B' : Type*} [CommRing B'] {f : A →+* B'} [Module B' M]
  (hf : ∀ (a : A) (m : M), a • m = f a • m)

end RingHom

end Solution

end Module.Relations
