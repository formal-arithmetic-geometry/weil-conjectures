/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights

/-!
# Extension bounds for mixed Frobenius modules

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-thm-dl-a1-upper`, lemma `lem-a1-extension-bounds`, order 3134 in
`main-20261015` (blueprint: lem-a1-extension-bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

/-- An extension of two Frobenius modules mixed of weights at most `w` is mixed
of weights at most `w`.

Source: Weil-conjectures blueprint, `sec-deligne-laumon-a1/sk-thm-dl-a1-upper`,
lemma `lem-a1-extension-bounds`, order 3134 in `main-20261015`
(blueprint: lem-a1-extension-bounds).

Proof: choose the finite Frobenius-stable filtrations of `A` and `C` supplied
by `def-weil-frobenius-module-weights`. Map the filtration of `A` into `B` by
`f`, and follow it by the inverse images under `g` of the filtration of `C`.
Injectivity of `f`, exactness at `B`, and surjectivity of `g` identify the
joining subspaces and the successive quotients with those of `A` and `C`.
Equivariance of both maps makes this a Frobenius-stable filtration with the
same induced Frobenius on those quotients. Every graded piece is therefore
pure of a weight at most `w`; the definition gives mixedness of `B`.
-/
theorem IsMixedOfWeightsAtMost.of_shortExact
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ)
    (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
    (C : FrobeniusModule.{u₃, v} Qlb)
    (f : A.carrier →ₗ[Qlb] B.carrier) (g : B.carrier →ₗ[Qlb] C.carrier)
    (hf : ∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x))
    (hg : ∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x))
    (hinj : Function.Injective f) (hexact : Function.Exact f g)
    (hsurj : Function.Surjective g) (w : ℝ)
    (hA : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w)
    (hC : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w := by
  sorry

end FrobeniusModule
