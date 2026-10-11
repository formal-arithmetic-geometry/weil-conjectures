/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.QuotSMulTop

/-! # Local criterion of flatness modulo a nonzerodivisor

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00ML and the remark
following it (blueprint: lem-weil-pbc-flat-local-criterion-nonzerodivisor).
-/

@[expose] public section

universe u v w

namespace RingTheory

/-- Local criterion of flatness modulo a nonzerodivisor.

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00ML and the remark
following it (blueprint: lem-weil-pbc-flat-local-criterion-nonzerodivisor).

The local homomorphism `φ` is `algebraMap A B`, and `M` is an `A`-module via `φ` by the
scalar tower, so `IsSMulRegular M x` is injectivity of multiplication by `φ(x)` on `M`.
`QuotSMulTop x M` is `M / xM`, a module over `A ⧸ Ideal.span {x} = A/xA`.

Proof (the two steps of the node):
1. Put `I = (x)`. Since `x` belongs to the maximal ideal, `I` is proper. Regularity of
   `x` makes the surjective map `A → I`, `a ↦ a * x`, injective, hence an isomorphism.
   Tensoring this isomorphism with `M` and using `A ⊗[A] M ≃ M` gives an isomorphism
   `β : M ≃ I ⊗[A] M` sending `m` to `x ⊗ m`. The multiplication map
   `μ : I ⊗[A] M → M`, `a ⊗ m ↦ φ(a) • m`, composed with `β`, is multiplication
   by `φ(x)`. This is injective by hypothesis, so `μ` is injective. This is the
   remark after Tag 00ML read through Remark Tag 00M6, which identifies Tor with
   the kernel of `μ`; no Tor construction is needed here.
2. The submodule `I • M` equals `xM`, and `A/I = A/xA`, so the quotient-flatness
   hypothesis is exactly flatness of `M/IM` over `A/I`
   (`def-weil-pbc-flat-ring-map`). Apply `lem-weil-pbc-flat-variant-local-criterion`
   (Tag 00ML) to the given local homomorphism of Noetherian local rings, the proper
   ideal `I`, and the finite `B`-module `M`, using injectivity of `μ` from step 1
   and quotient flatness. It gives flatness of `M` over `A`.
-/
theorem flat_of_localCriterion_nonzerodivisor
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (x : A) (hx_mem : x ∈ IsLocalRing.maximalIdeal A)
    (hx_reg : x ∈ nonZeroDivisors A) (hxM : IsSMulRegular M x)
    (hquot : Module.Flat (A ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Flat A M := by
  sorry

end RingTheory
