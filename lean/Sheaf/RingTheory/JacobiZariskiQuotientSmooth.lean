/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-! # Jacobi–Zariski sequence for a quotient of a smooth algebra

Source: Stacks Project, Algebra, Lemma Tags 00S2, 07BP and 00RU
(blueprint: lem-weil-pbc-jacobi-zariski-quotient-smooth).
-/

@[expose] public section

universe u v
open scoped TensorProduct

namespace Algebra

/--
Source: Stacks Project, Algebra, Lemma Tag 00S2, with Tags 07BP and 00RU
(blueprint: lem-weil-pbc-jacobi-zariski-quotient-smooth).
Proof:
1. Apply lem-weil-pbc-jacobi-zariski-homology-sequence to A → B → C (Tag 00S2).
2. Use lem-weil-pbc-jacobi-zariski-surjection-h1 and
   lem-weil-pbc-jacobi-zariski-surjection-differentials (Tag 07BP) to identify
   the relative first homology with a.Cotangent and the relative differentials with zero.
3. Apply lem-weil-pbc-jacobi-zariski-left-term-vanishing: projectivity kills
   the two Tor groups, and the first homology vanishing kills the left endpoint.
4. Use lem-weil-pbc-jacobi-zariski-differential-maps (Tag 00RU) for the two
   displayed formulas. Truncate the sequence at its zero endpoints.
-/
theorem jacobiZariski_quotient_smooth
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton (H1Cotangent A B)] [Module.Projective B (KaehlerDifferential A B)]
    (a : Ideal B) :
    let C := B ⧸ a
    ∃ (i : H1Cotangent A C →ₗ[C] a.Cotangent)
      (δ : a.Cotangent →ₗ[C] C ⊗[B] KaehlerDifferential A B)
      (w : C ⊗[B] KaehlerDifferential A B →ₗ[C] KaehlerDifferential A C),
      Function.Injective i ∧ Function.Exact i δ ∧ Function.Exact δ w ∧
      Function.Surjective w ∧
      (∀ x : a, δ (a.toCotangent x) = 1 ⊗ₜ[B] KaehlerDifferential.D A B x) ∧
      (∀ (c : C) (b : B), w (c ⊗ₜ[B] KaehlerDifferential.D A B b) =
        c • KaehlerDifferential.D A C (Ideal.Quotient.mk a b)) := by
  sorry

end Algebra
