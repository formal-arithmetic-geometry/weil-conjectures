module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Prime

/-!
# Prime-factor descent along a lattice-support retraction

Source: agent-formulated auxiliary extracted from the original proof of
`lem-trf-complete-toric-boundary-class-injectivity`, steps 9--11.
ILO, Expose VI, 1.4 and 1.6(i)--(ii), printed pages 69--70, provides the local-model
context only; this abstract lemma is not attributed to ILO or Kato.
(blueprint: lem-trf-lattice-retraction-prime-factor-descent)
-/

@[expose] public section

universe u

namespace RingTheory

/-- Descent of a factor of a prime monomial through a subring-linear retraction.
Source: the agent argument extracted from the original boundary-class proof, steps 9--11;
ILO VI 1.4 and 1.6, printed pages 69--70, supplies context only.
(blueprint: lem-trf-lattice-retraction-prime-factor-descent)

Proof plan:
1. Apply `mul_eq_mul_prime_prod` (lem-trf-prime-product-factor-splitting) with coefficient
   one to the finite set of labelled copies `(i,j)` with `j < s i`. Regroup the chosen
   subproduct to get `e ≤ s` and `h = x^e v`, with `v` a unit. Repeated or associated
   primes are allowed.
2. Put `N = ∑ i, e i` and `a i = N * w i - e i`. Positivity of `w` makes this a natural
   vector, with `a + e = Nw`. If `e` is outside `M`, then `a` is outside `M` as well.
3. In that case support vanishing and linearity with scalar `h` give `ρ(x^a h) = 0`.
   Linearity with scalar `x^(Nw)`, which belongs to `R`, instead gives
   `ρ(x^a h) = x^(Nw) ρ(v)`. This is nonzero since the prime elements are nonzero and
   `ρ(v)` is a unit. This contradiction puts `e` in `M`.
4. Now `x^e` belongs to `R`; apply the retraction to `h = x^e v` to get
   `h = x^e ρ(v)` in `R`. Set `u = ρ(v)`, a unit by hypothesis. Empty coordinates and
   zero exponents use the same formulas, with empty product one and empty sum zero. -/
theorem latticeRetraction_prime_factor_descent
    {D : Type u} [CommRing D] [IsDomain D] (R : Subring D)
    (r : ℕ) (x : Fin r → D) (hx : ∀ i : Fin r, Prime (x i))
    (M : AddSubgroup (Fin r → ℤ))
    (hmon : ∀ a : Fin r → ℕ, (fun i ↦ (a i : ℤ)) ∈ M →
      (∏ i : Fin r, x i ^ a i) ∈ R)
    (ρ : D →ₗ[R] R) (hρ : ∀ z : R, ρ (z : D) = z)
    (hsupport : ∀ a : Fin r → ℕ, (fun i ↦ (a i : ℤ)) ∉ M →
      ρ (∏ i : Fin r, x i ^ a i) = 0)
    (hunits : ∀ v : Dˣ, IsUnit (ρ (v : D)))
    (w : Fin r → ℕ) (hw : (fun i ↦ (w i : ℤ)) ∈ M)
    (hwpos : ∀ i : Fin r, 0 < w i)
    (s : Fin r → ℕ) (hs : (fun i ↦ (s i : ℤ)) ∈ M)
    (h h' : R) (hh : (h : D) * (h' : D) = ∏ i : Fin r, x i ^ s i) :
    ∃ (e : Fin r → ℕ) (he : (fun i ↦ (e i : ℤ)) ∈ M) (v : Dˣ) (u : Rˣ),
      e ≤ s ∧
      (h : D) = (∏ i : Fin r, x i ^ e i) * (v : D) ∧
      (u : R) = ρ (v : D) ∧
      h = (⟨∏ i : Fin r, x i ^ e i, hmon e he⟩ : R) * (u : R) := by
  sorry

end RingTheory
