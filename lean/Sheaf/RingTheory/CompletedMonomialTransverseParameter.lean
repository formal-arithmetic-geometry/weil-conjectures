/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.CompleteToricModel
public import Mathlib.Algebra.BigOperators.Finprod
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.TraceFormula.SharpMonoidPositiveGrading
import Sheaf.RingTheory.MonoidCompletionCoefficients
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Transverse parameters modulo completed monomial ideals

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VIII, proof of
Lemma 3.4.13(i), printed pp. 112--113, and Exposé VI 1.6(i)--(ii), printed p. 70
(blueprint: lem-per-completed-monomial-transverse-parameter).

The completion, chart monomials and completed chart ideal are the existing
`ToricMonoid` constructions. Coefficient families use Mathlib's `MvPowerSeries`;
the multiplication formula below is convolution in the monoid index, not the
pointwise multiplication instance on a function type.
-/

@[expose] public section

set_option autoImplicit false

universe u v

noncomputable section

namespace ToricMonoid

/-- The ideal `K = (z^h : h ∈ H) B` in the specified completed monoid polynomial ring.
The definition allows the empty and the whole monoid ideal.
Source: ILO VIII, proof of Lemma 3.4.13(i), printed pp. 112--113
(blueprint: lem-per-completed-monomial-transverse-parameter). -/
def completedMonomialIdeal (L : Type v) [CommRing L] [IsLocalRing L]
    (Q : Type u) [AddCommMonoid Q] (n : ℕ) (H : Set Q) : Ideal (Complete L Q n) :=
  Ideal.span {b | ∃ h ∈ H, b = monomial L Q n h}

/-- The transverse variable `t_i`, the image of the corresponding polynomial variable
under the canonical completion map.
Source: ILO VI 1.6(i)--(ii), printed p. 70, and VIII 3.4.13(i), printed p. 113
(blueprint: lem-per-completed-monomial-transverse-parameter). -/
def parameter (L : Type v) [CommRing L] [IsLocalRing L]
    (Q : Type u) [AddCommMonoid Q] (n : ℕ) (i : Fin n) : Complete L Q n :=
  algebraMap (PolynomialRing L Q n) (Complete L Q n) (MvPolynomial.X i)

open Classical in
/-- Unique series expansions off a monoid ideal, the monomial membership criterion,
and regularity of the first transverse parameter, also after a Cohen equation.

Source: ILO VIII, proof of Lemma 3.4.13(i), printed pp. 112--113, with the
completed local models of VI 1.6(i)--(ii), printed p. 70
(blueprint: lem-per-completed-monomial-transverse-parameter).

`hQ` is the recorded fs predicate applied through the multiplicative type tag;
`hsharp` says that zero is the only additive unit. `hH` is `H + Q ⊆ H`.
`hL` allows exactly a field or a Cohen ring; localness is intrinsic in both cases.
`c` supplies all monoid coefficients in `L[[t]]`, normalized on every polynomial
monomial and with convolution multiplication. The linear equivalence `e`, compatible
with `c` on every representative, states existence and uniqueness of the expansion
in `B/K`. Thus no choice of a representative is used to define its coefficients.
`Fin n` uses zero-based indices: `⟨0, hn⟩` is precisely `t₁`; the parameter
assertions are vacuous when `n = 0`.

Proof plan (the five steps of the DAG node):
1. The zero face of the sharp fs monoid is a face. Apply
   `lem-trf-fs-face-sharpening` and `lem-trf-sharp-monoid-positive-grading` to
   obtain a positive integral grading on its finite free group completion.
   Add total variable degree to grade `Q ⊕ ℕⁿ`. A field is a complete Noetherian
   local domain; a Cohen ring is one by its definition and
   `lem-weil-pbc-pid-noetherian-normal`. Apply
   `lem-trf-monoid-completion-coefficients` to identify the completion with all
   coefficient families, with finite convolution.
2. Regroup the coefficients using `def-weil-pbc-multivariate-power-series`.
   Monoid-ideal stability makes products by `z^h` supported in `H`.
   `lem-trf-sharp-monoid-ideal-minimal-generators` supplies finitely many
   generators of `H`. Partition its supported coefficients according to a
   generator dividing the exponent, and factor out that generator. This proves
   exactly the membership criterion and the quotient equivalence `e`, including
   `H = ∅` and `H = Q`.
3. For nonzero `x` modulo `K`, choose an exponent off `H` of minimal positive
   grading with nonzero coefficient, using
   `lem-trf-positive-monoid-adic-filtration`. The corresponding coefficient of
   `f * x` is `c f 0` times this coefficient: all positive monoid contributions
   involve smaller degrees. The power-series ring over a domain is a domain,
   as seen by the total-degree-then-lexicographic least terms. This product is
   nonzero, proving injectivity.
4. Take `f = t₁`, whose coefficient at `z^0` is the nonzero series `t₁`.
5. In the Cohen case evaluate at `t₁ = 0` on `B/K`. Its kernel is `t₁(B/K)`.
   The coefficient at `z^0` of the reduced equation is `p` plus a series in the
   remaining variables with zero constant coefficient, hence nonzero. Step 3
   makes this reduced equation regular. From `t₁ x = θ y`, reduction forces
   `y = t₁ y₁`; cancellation by Step 4 then gives `x = θ y₁`. This is precisely
   injectivity modulo `K + θ B`. For `n = 0` this clause is vacuous.
-/
theorem completedMonomial_transverse_parameter
    (Q : Type u) [AddCommMonoid Q]
    (hQ : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative Q))
    (hsharp : ∀ q : Q, IsAddUnit q → q = 0)
    (H : Set Q) (hH : ∀ h ∈ H, ∀ q : Q, h + q ∈ H) (n : ℕ)
    (L : Type v) [CommRing L] [IsLocalRing L]
    (hL : IsField L ∨ ∃ p : ℕ, IsCohenRing p L) :
    ∃ c : Complete L Q n ≃ₗ[L] (Q → MvPowerSeries (Fin n) L),
      (∀ (q r : Q) (a : L) (E : Fin n →₀ ℕ),
        c (algebraMap (PolynomialRing L Q n) (Complete L Q n)
          (MvPolynomial.monomial E (AddMonoidAlgebra.single q a))) r =
            if r = q then MvPowerSeries.monomial E a else 0) ∧
      (∀ (x y : Complete L Q n) (q : Q),
        c (x * y) q = ∑ᶠ d : {d : Q × Q // d.1 + d.2 = q},
          c x d.1.1 * c y d.1.2) ∧
      ∃ e : (Complete L Q n ⧸ completedMonomialIdeal L Q n H) ≃ₗ[L]
          ({q : Q // q ∉ H} → MvPowerSeries (Fin n) L),
        (∀ (x : Complete L Q n) (q : {q : Q // q ∉ H}),
          e (Ideal.Quotient.mk (completedMonomialIdeal L Q n H) x) q = c x q.1) ∧
        (∀ x : Complete L Q n,
          x ∈ completedMonomialIdeal L Q n H ↔ ∀ q : Q, q ∉ H → c x q = 0) ∧
        (∀ f : Complete L Q n, c f 0 ≠ 0 →
          Function.Injective
            (fun x : Complete L Q n ⧸ completedMonomialIdeal L Q n H ↦
              Ideal.Quotient.mk (completedMonomialIdeal L Q n H) f * x)) ∧
        (∀ hn : 0 < n,
          Function.Injective
            (fun x : Complete L Q n ⧸ completedMonomialIdeal L Q n H ↦
              Ideal.Quotient.mk (completedMonomialIdeal L Q n H)
                (parameter L Q n ⟨0, hn⟩) * x)) ∧
        (∀ (p : ℕ), IsCohenRing p L → ∀ θ : Complete L Q n,
          θ - (p : Complete L Q n) ∈ completedChartIdeal L Q n →
          ∀ hn : 0 < n,
            Function.Injective
              (fun x : Complete L Q n ⧸
                  (completedMonomialIdeal L Q n H ⊔ Ideal.span {θ}) ↦
                Ideal.Quotient.mk
                  (completedMonomialIdeal L Q n H ⊔ Ideal.span {θ})
                  (parameter L Q n ⟨0, hn⟩) * x)) := by
  sorry

end ToricMonoid
