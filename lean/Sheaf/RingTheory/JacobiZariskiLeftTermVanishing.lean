/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Vanishing of the left base-change term of the Jacobi-Zariski sequence

Source: Stacks Project, Algebra, Lemma 00S2, final assertion and its proof
(blueprint: lem-weil-pbc-jacobi-zariski-left-term-vanishing).
-/

@[expose] public section

universe u v

open TensorProduct

namespace Algebra

/-- (blueprint: lem-weil-pbc-jacobi-zariski-left-term-vanishing)
Stacks Project, Algebra, Lemma 00S2, final assertion, specialized to projective differentials
and zero first cotangent homology. The presentation is the canonical `A[B] → B`.
The tensor of the kernel inclusion is injective and identifies its source with the kernel
of the tensored differential; both modules vanish.

Proof: put `M = range δ`. The cokernel of `δ` is `Ω[B⁄A]` by
`lem-weil-pbc-naive-cotangent-complex-cokernel-kahler`, giving exact sequences
`0 → H₁ → N₁ → M → 0` and `0 → M → N₀ → Ω[B⁄A] → 0`.
The latter quotient is projective and hence flat by `lem-weil-pbc-projective-module-flat`;
`N₀` is free, hence flat. Thus `M` is flat by `lem-weil-pbc-flat-ses-kernel-flat`.
By `lem-weil-pbc-flat-quotient-tensor-injective`, tensoring both sequences with `B ⧸ a`
preserves their exactness and their left injections. Factoring the tensored differential
through `M ⊗[B] (B ⧸ a)` identifies its kernel with the image of the tensored kernel
inclusion. Finally `H₁ = 0` implies that its tensor is zero, and hence so is this kernel. -/
theorem jacobiZariski_leftTerm_vanishing
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton (H1Cotangent A B)] [Module.Projective B (KaehlerDifferential A B)]
    (a : Ideal B) :
    let P := (Generators.self A B).toExtension
    let δ := P.cotangentComplex.rTensor (B ⧸ a)
    let ι := P.h1Cotangentι.rTensor (B ⧸ a)
    Function.Injective ι ∧ LinearMap.range ι = LinearMap.ker δ ∧
      Nonempty ((LinearMap.ker δ) ≃ₗ[B] (H1Cotangent A B ⊗[B] (B ⧸ a))) ∧
      Subsingleton (H1Cotangent A B ⊗[B] (B ⧸ a)) ∧
      Subsingleton (LinearMap.ker δ) := by
  sorry

end Algebra
