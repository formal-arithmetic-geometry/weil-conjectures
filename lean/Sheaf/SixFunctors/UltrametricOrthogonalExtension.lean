/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension

/-! # Orthogonality of a nearest-point residual

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
auxiliary nearest-point residual calculation
(blueprint: lem-sfb-ultrametric-orthogonal-extension).
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u v

namespace Padic

/-- A nearest-point residual extends a finite orthogonal family over a finite
extension of `ℚ_[ℓ]`.

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
auxiliary nearest-point residual calculation
(blueprint: lem-sfb-ultrametric-orthogonal-extension).

Proof: Let `b = x - w`. Definiteness and `x ∉ W` give `b ≠ 0` and positive
norm. Minimality gives `‖b‖ ≤ ‖x-z‖` for every `z ∈ W`. For `u ∈ W` and
`a ∈ E`, this yields the lower bound `‖u + a b‖ ≥ |a|_E ‖b‖`; applying the
ultrametric inequality to `u = (u + a b) - a b` gives the other lower bound,
so `‖u + a b‖ = max (‖u‖, |a|_E ‖b‖)`. Substitution of the old orthogonality
formula proves the enlarged formula, including `n = 0`. The formula and
`b ≠ 0` give linear independence, and `b = x - w` gives the asserted span.
-/
theorem ultrametric_orthogonal_extension
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (V : Type v) [AddCommGroup V] [Module E V]
    (norm : V → NNReal)
    (hscale : ∀ (a : E) (z : V),
      norm (a • z) = Real.toNNReal (coefficientExtensionAbsoluteValue l E a) * norm z)
    (htriangle : ∀ (z₁ z₂ : V),
      norm (z₁ + z₂) ≤ max (norm z₁) (norm z₂))
    (hdefinite : ∀ z : V, norm z = 0 ↔ z = 0)
    (n : ℕ) (b : Fin n → V) (hlin : LinearIndependent E b)
    (horth : ∀ (a : Fin n → E),
      norm (∑ i, a i • b i) =
        Finset.univ.sup (fun i =>
          Real.toNNReal (coefficientExtensionAbsoluteValue l E (a i)) * norm (b i)))
    (x : V) (hx : x ∉ (Submodule.span E (Set.range b) : Set V))
    (w : V) (hw : w ∈ Submodule.span E (Set.range b))
    (hmin : norm (x - w) =
      sInf (Set.image (fun z : V => norm (x - z))
        (Submodule.span E (Set.range b) : Set V))) :
    x - w ≠ 0 ∧
      (∀ (a : Fin (n + 1) → E),
        norm (∑ i, a i • Fin.snoc (α := fun _ => V) b (x - w) i) =
          Finset.univ.sup (fun i =>
            Real.toNNReal (coefficientExtensionAbsoluteValue l E (a i)) *
              norm (Fin.snoc (α := fun _ => V) b (x - w) i))) ∧
      LinearIndependent E (Fin.snoc (α := fun _ => V) b (x - w)) ∧
      Submodule.span E (Set.range (Fin.snoc (α := fun _ => V) b (x - w))) =
        Submodule.span E (Set.range b) + Submodule.span E ({x} : Set V) := by
  sorry

end Padic
