/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Roots of a split binomial as scalar multiples of roots of unity

Source: Stacks Project, fields.tex, Tag 09I6, section-Kummer, opening paragraph;
the elementary separable-binomial input, without irreducibility.
(blueprint: lem-sfb-split-binomial-root-torsor)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Polynomial

namespace Polynomial

/-- The roots of a nonzero binomial form the scalar translate of the base roots of unity.

Source: Stacks Project, fields.tex, Tag 09I6, section-Kummer, opening paragraph;
the elementary root-scaling input to the one-root Kummer construction.
(blueprint: lem-sfb-split-binomial-root-torsor)

Proof: For each nonzero b, the polynomial f_b = X^n - b is monic of degree n and
has derivative n X^(n-1). The identity
-b⁻¹ f_b + (n b)⁻¹ X f_b' = 1 proves separability, using
[def-pc-separable-polynomial]. Apply
[lem-pc-separable-polynomial-distinct-roots-alg-closed] to f_a and f_1 in the
algebraic closure: each has n distinct roots and is the product of its linear factors.
The splitting hypothesis for f_1 implies that all its roots in the closure are images
of elements of F: evaluating its split factorization gives a vanishing factor.
These roots are nonzero and form precisely the subgroup `rootsOfUnity n F`, so its
cardinality is n. If alpha^n = a, then alpha is nonzero. Multiplication by alpha
sends each base root of unity to a root of f_a. Conversely, beta^n = a implies
(beta / alpha)^n = 1; the preceding descent places this quotient in the base root
group. Division by alpha and multiplication by alpha are inverse, giving the claimed
equivalence with the prescribed formula. Reindex the distinct-root factorization by
this equivalence. Finally specialize to a = 1 and alpha = 1.

`NeZero n` expresses n ≥ 1. The finite product uses Mathlib's canonical finiteness
instance for the subgroup of roots of unity; no enumeration or primitive root is chosen.
-/
theorem split_binomial_root_torsor (F : Type u) [Field F] (n : ℕ) [NeZero n]
    (hn : IsUnit (n : F)) (hsplit : (X ^ n - 1 : F[X]).Splits)
    (Ω : Type v) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] :
    Nat.card (rootsOfUnity n F) = n ∧
      (∀ a : Fˣ,
        (X ^ n - C (a : F)).Monic ∧
        (X ^ n - C (a : F)).Separable ∧
        ∀ α : Ω, α ^ n = algebraMap F Ω (a : F) →
          α ≠ 0 ∧
          (∃ e : rootsOfUnity n F ≃ {β : Ω // β ^ n = algebraMap F Ω (a : F)},
            ∀ ζ : rootsOfUnity n F,
              (e ζ : Ω) = α * algebraMap F Ω ((ζ : Fˣ) : F)) ∧
          (X ^ n - C (algebraMap F Ω (a : F)) : Ω[X]) =
            ∏ ζ ∈ @Finset.univ (rootsOfUnity n F) (Fintype.ofFinite _),
              (X - C (α * algebraMap F Ω ((ζ : Fˣ) : F)))) ∧
      (X ^ n - 1 : Ω[X]) =
        ∏ ζ ∈ @Finset.univ (rootsOfUnity n F) (Fintype.ofFinite _),
          (X - C (algebraMap F Ω ((ζ : Fˣ) : F))) := by
  sorry

end Polynomial
