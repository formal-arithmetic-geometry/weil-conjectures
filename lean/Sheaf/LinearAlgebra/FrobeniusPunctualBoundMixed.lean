/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.LinearAlgebra.SpectrumExactSequence

/-!
# Punctual bounds give mixed Frobenius modules

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-thm-dl-a1-upper`, lemma `lem-a1-punctual-bound-module-mixed`
(blueprint: lem-a1-punctual-bound-module-mixed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace FrobeniusModule

/-- A bound on every Frobenius eigenvalue gives a finite stable filtration with pure
successive quotients of weights at most `w`.

Source: Weil-conjectures blueprint, `sec-deligne-laumon-a1/sk-thm-dl-a1-upper`,
`lem-a1-punctual-bound-module-mixed`
(blueprint: lem-a1-punctual-bound-module-mixed).

Proof: choose a Jordan–Holder filtration of the finite-dimensional Frobenius module.
Every nonzero simple quotient is one-dimensional: over the algebraically closed coefficient
field it has an eigenvector, whose span is a nonzero stable subspace, hence is the whole
simple quotient. By `lem-a1-spectrum-exact-sequence`, the single eigenvalue of each quotient
is an eigenvalue of the original Frobenius, so its complex norm is at most `q ^ (w / 2)`.
The eigenvalue is nonzero because Frobenius is invertible. Since `q = p ^ a > 1`, assign this
quotient the real weight `2 * log (norm (iota eigenvalue)) / log q`; the bound implies that
this weight is at most `w`, and the quotient is pure of that weight by
`def-weil-frobenius-module-weights`. These quotients and their induced automorphisms exhibit
the required mixed filtration. For the zero module use the length-zero filtration. -/
theorem isMixedOfWeightsAtMost_of_forall_hasEigenvalue
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ) (M : FrobeniusModule.{u, v} Qlb) (w : ℝ)
    (h : ∀ α : Qlb, M.frobeniusEnd.HasEigenvalue α →
      ‖iota α‖ ≤ ((p ^ a : ℕ) : ℝ) ^ (w / 2)) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w := sorry

end FrobeniusModule
