/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.Smooth.Field

/-! # Coefficient lifting and principal formal polynomial presentations

Source: Temkin, Excellent Desingularization, Propositions 3.2.1 and 3.2.3, printed pp.18--19
(blueprint: lem-per-principal-formal-coefficient-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

/-- The completion of `k[t,x₁,...,xᵣ]` along `(t)`, written as multivariate polynomials
in `r` variables over `k[t]`. This is the source ring in Temkin, Excellent Desingularization,
Proposition 3.2.3, printed p.19 (blueprint: lem-per-principal-formal-coefficient-presentation).
The algebra structure is Mathlib's canonical structure on adic completion. -/
abbrev principalFormalPolynomialRing (k : Type u) [CommRing k] (r : ℕ) :=
  AdicCompletion
    (Ideal.span {MvPolynomial.C Polynomial.X} : Ideal (MvPolynomial (Fin r) (Polynomial k)))
    (MvPolynomial (Fin r) (Polynomial k))

/-- A characteristic-zero coefficient map on the reduced closed fibre lifts, and the resulting
principal formal variety has a finite completed polynomial presentation.
Source: Temkin, Excellent Desingularization, Propositions 3.2.1 and 3.2.3, printed pp.18--19
(blueprint: lem-per-principal-formal-coefficient-presentation).

Proof plan:
1. For the zero ring take the unique coefficient map and the unique surjection, with `r = 0`.
   Otherwise put `J = radical (π)`. Choose generators `zᵢ` and powers `zᵢ^eᵢ ∈ (π)`.
   The pigeonhole argument with `N = 1 + ∑ (eᵢ - 1)` gives `J^N ≤ (π)`; use `N = 1`
   when the generating list is empty (def-weil-pbc-noetherian-ring).
2. The inclusions `(π)^n ≤ J^n` and `J^(N*n) ≤ (π)^n` identify the two rings of compatible
   residues. Thus `B` is also `J`-adically complete. Separatedness and `B ≠ 0` imply `J ≠ ⊤`
   (def-weil-pbc-adic-completion).
3. Every nonzero integer is invertible modulo `J`. Lift an inverse and sum the geometric
   series of its error in `J`; its powers tend to zero by Step 1. This makes `B` and its
   quotients rational algebras, compatibly with the specified coefficient map.
4. Lift the specified map successively from `B/J^m` to `B/J^(m+1)`. The kernel is square-zero,
   so formal smoothness of the characteristic-zero field over the rationals gives each lift
   (lem-weil-pbc-char-zero-field-extension-formally-smooth). Their compatible limit is `s`.
5. Lift finite algebra generators of `B/J`, and append the `zᵢ`. Their polynomial image `R`
   satisfies `B = R + J` and `J^m ⊆ R + J^(m+1)`. Hence `B = R + J^N`, so `B = R + (π)`:
   every residue modulo `(π)` lies in `R`. This proves finite type of `B/(π)`
   (def-weil-pbc-finite-type-algebra, def-weil-pbc-mv-polynomial-ring).
6. Evaluate `t` at `π` and the remaining variables at these lifts. The induced maps modulo
   `t^n` and `π^n` commute with reduction, so their limit gives `q`. It commutes with the
   `k[t]` structure maps and takes `t^n P` into `π^n B`, giving the required continuity
   (def-weil-pbc-adic-completion, def-weil-pbc-mv-polynomial-ring).
7. Given `b`, successively write `cⱼ - hⱼ = π*cⱼ₊₁`, starting with `c₀ = b`, using Step 5.
   The partial sums `∑ t^j hⱼ` define a compatible element of the completion whose image is
   congruent to `b` modulo every `π^n`. Separatedness gives equality and therefore surjectivity.
   This uses no cancellation of `π`, including when it is zero, nilpotent or a zero divisor.
-/
theorem exists_principal_formal_coefficient_presentation
    (B : Type v) [CommRing B] [IsNoetherianRing B] (π : B)
    [IsAdicComplete (Ideal.span {π}) B]
    (k : Type u) [Field k] [CharZero k]
    (s₀ : k →+* B ⧸ (Ideal.span {π}).radical) (hs₀ : s₀.FiniteType) :
    ∃ s : k →+* B,
      (Ideal.Quotient.mk (Ideal.span {π}).radical).comp s = s₀ ∧
      ((Ideal.Quotient.mk (Ideal.span {π})).comp s).FiniteType ∧
      ∃ (r : ℕ) (q : principalFormalPolynomialRing k r →+* B),
        Function.Surjective q ∧
        q.comp (algebraMap (Polynomial k) (principalFormalPolynomialRing k r)) =
          Polynomial.eval₂RingHom s π ∧
        @Continuous (principalFormalPolynomialRing k r) B
          (Ideal.span {algebraMap (Polynomial k) (principalFormalPolynomialRing k r)
            Polynomial.X}).adicTopology
          (Ideal.span {π}).adicTopology q := by
  sorry

end RingTheory
