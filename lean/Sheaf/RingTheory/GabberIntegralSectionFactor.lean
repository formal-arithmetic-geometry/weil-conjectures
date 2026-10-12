module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Idempotents
import Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization
import Sheaf.RingTheory.EtaleSectionIdempotentSplitting
import Sheaf.RingTheory.FiniteGabberPolynomial

@[expose] public section

universe u v

open Polynomial
open scoped BigOperators

namespace Algebra

/-- Gabber's root condition constructs an integral idempotent factor of an étale algebra,
with the prescribed section on the closed fibre. This stops before identifying that factor
with the base ring.

Source: Stacks Project, Tag 09XI, proof of (5) ⇒ (2), construction of the integral factor
(https://stacks.math.columbia.edu/tag/09XI).
(blueprint: lem-weil-pbc-gabber-root-criterion-integral-section-factor)

Proof:
1. Factor σ through B/IB. Étale base change and the étale-section idempotent splitting
produce an idempotent ε whose localization is A/I, with σ the first projection.
2. Apply the integral-closure finite-fibre localization theorem (09XH) to this finite
factor. It gives ε' in B'/IB', where B' is the integral closure, and a lift b with
B'_b ≅ B_b, compatibly with ε and the chosen section.
3. Choose finitely many numerators generating B'_b over A and finitely many elements
expressing b²-b in IB'. The subalgebra B'' they generate together with b is finite
because all its generators are integral. Then B''_b ≅ B'_b; the image of b in B''/IB''
is idempotent, and its first factor is A/I, since quotient commutes with localization.
4. The finite Gabber polynomial theorem (0EM0) gives a monic f annihilating b, of form
X^n(X-1) plus I-coefficients, with n ≥ 1. Choose the root α in 1+I using hroots.
Write f = (X-α)g. Modulo I, g = X^n, so g(α) and α lie in 1+I and are units.
Put E = g(α)⁻¹g. Since g(X)-g(α) is divisible by X-α, f divides E²-E and
(X-α)E. Thus d = E(b) in B' is idempotent and bd = αd. Modulo I, d is ε',
because E reduces to X^n and ε' is idempotent with n ≥ 1.
5. Let e be the image of d in B. On the d-factor, b equals the unit α, so the
isomorphism B'_b ≅ B_b restricts to B'_d ≅ B_e. Localization at an idempotent is
a quotient; therefore B'_d, and hence B_e, is integral over A.
6. The reduction of e is ε, so B_e/IB_e ≅ (B/IB)_ε ≅ A/I compatibly with the
structure map. This proves bijectivity of the quotient map in the conclusion.
Since σ(e)=1, σ extends uniquely over B_e by localization, giving ρ with the
stated equality on every x. No isomorphism A ≅ B_e is used in this construction. -/
theorem exists_gabber_integral_section_factor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (hroots : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → A),
      (∀ j, a j ∈ I) → ∀ (f : A[X]), f.Monic →
        f = X ^ n * (X - 1) + ∑ j : Fin (n + 1), C (a j) * X ^ (j : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (B : Type v) [CommRing B] [Algebra A B] [Etale A B] (σ : B →ₐ[A] A ⧸ I) :
    ∃ e : B, IsIdempotentElem e ∧
      (algebraMap A (Localization.Away e)).IsIntegral ∧
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap A (Localization.Away e)) I)
          (algebraMap A (Localization.Away e)) Ideal.le_comap_map) ∧
      ∃ ρ : Localization.Away e →ₐ[A] A ⧸ I,
        ∀ x : B, ρ (algebraMap B (Localization.Away e) x) = σ x := by
  sorry

end Algebra
