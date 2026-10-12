/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Sheaf.FieldTheory.ExistsPBasis
import Sheaf.FieldTheory.IntersectionSubfieldsSubspace
import Sheaf.FieldTheory.PBasisDifferentialsBasis
import Sheaf.FieldTheory.PIndependentDifferentialsIndependent

/-! # Differential kernel detection

Source: Stacks Project, More on Algebra, Tag 07P4.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-kernel)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
namespace FieldTheory
local instance zmodAlgebraKernel (p : ℕ) (K : Type u) [Field K] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra (R := K) p

/-- Differential kernel detection.
Source: Stacks Project, More on Algebra, Tag 07P4 (`lemma-intersection-subfields`),
`literature/stacks-project/more-algebra.tex`.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-kernel)

Proof:

1. Frobenius is an injective ring homomorphism, so `K^p` and `L^p` are subfields, and the
prime field lies in `K^p`. Choose a p-basis `x_i` of `K` over the prime field using
`lem-weil-pbc-p-basis-exists`. Its p-monomials form a basis over `K^p`, and `dx_i` form a
basis of the absolute differentials by `lem-weil-pbc-p-basis-differentials-basis`.

2. If a nonzero differential dies in every relative module, express it with finite nonempty
support in the `dx_i`. By `lem-weil-pbc-p-independent-differentials-independent`, its
support's p-monomials have a nontrivial relation over each `Kα`. The space of relations
therefore meets every `Kα^N` nontrivially. The index family is nonempty: otherwise the
intersection condition makes `K` perfect, contradicting the nonempty p-basis support.
Apply `lem-weil-pbc-intersection-subfields-subspace` to obtain a nontrivial relation over
`K^p`, contradicting the p-basis monomials' independence. This proves the first clause. -/
theorem intersection_subfields_differentials_kernel
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    {ι : Type v} (Kα : ι → IntermediateField (ZMod p) K)
    (h₁ : ∀ α : ι, Set.range (fun x : K => x ^ p) ⊆ (Kα α : Set K))
    (h₂ : Set.range (fun x : K => x ^ p) =
      ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K))
    (h₃ : ∀ α β : ι, ∃ γ : ι, Kα γ ≤ Kα α ⊓ Kα β) :
    ∀ ω : Ω[K⁄ZMod p],
      (∀ α : ι, KaehlerDifferential.map (ZMod p) (Kα α) K K ω = 0) → ω = 0 := by
  sorry
end FieldTheory
