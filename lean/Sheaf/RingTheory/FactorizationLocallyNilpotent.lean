/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Unique lifting of coprime monic factorizations modulo locally nilpotent ideals

Source: Stacks Project, More on Algebra, Tag 0ALI, final factorization paragraph
(blueprint: lem-weil-pbc-henselian-factorization-locally-nilpotent).
Existence is the Stacks assertion; uniqueness is the agent-written argument of the DAG node.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A coprime monic factorization modulo an ideal whose elements are nilpotent lifts uniquely.
Source: Stacks Project, Tag 0ALI, final paragraph, for existence; the DAG's agent-written
uniqueness argument (blueprint: lem-weil-pbc-henselian-factorization-locally-nilpotent).

Proof:
1. The ideal `J` lies in the Jacobson radical: if a nilpotent element `x` were outside a
   maximal ideal, write `1 = a*x + m`. The finite geometric series makes `m = 1 - a*x`
   a unit, contradicting its membership in that maximal ideal.
2. For any finite `A`-algebra `B`, the ideal `JB` is locally nilpotent by
   `lem-weil-pbc-locally-nilpotent-extension`. Idempotents lift uniquely across it by
   `lem-weil-pbc-lift-idempotents-locally-nilpotent`. Thus `(A,J)` is a henselian pair
   in the sense of `def-weil-pbc-henselian-terminology`.
3. Apply `lem-weil-pbc-henselian-factorization-criterion` to obtain the monic factors.
4. Coprimality lifts when one factor is monic: `A[T]/(g,k)` is a finite `A`-module by
   `lem-weil-pbc-monic-quotient-free`, and its reduction modulo `J` vanishes.
   Nakayama (`lem-weil-pbc-nakayama-jacobson`) makes this module zero, giving
   polynomials `a,b` with `a*g + b*k = 1`.
5. Given two lifts `f = g*h = g'*h'`, step 4 applied to `g,h'` shows that `g` divides `g'`.
   If `A` is the zero ring uniqueness is immediate. Otherwise `A/J` is nonzero, so reduction
   preserves monic degrees, and `g,g'` have the same degree. Writing `g' = g*q`, comparison
   of leading coefficients and degrees makes `q` monic of degree zero, hence `q = 1`.
   Thus `g = g'`; cancel the monic polynomial `g` to get `h = h'`.
-/
theorem existsUnique_monic_factorization_of_locally_nilpotent
    {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : ∀ x : A, x ∈ J → IsNilpotent x)
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ J)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk J) = g₀ * h₀) :
    ∃! gh : A[X] × A[X],
      gh.1.Monic ∧ gh.2.Monic ∧ f = gh.1 * gh.2 ∧
        gh.1.map (Ideal.Quotient.mk J) = g₀ ∧ gh.2.map (Ideal.Quotient.mk J) = h₀ := by
  sorry

end Polynomial
