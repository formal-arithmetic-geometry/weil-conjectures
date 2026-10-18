/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.CompleteToricKatoRecognition

/-!
# Factors of monomials in complete toric local models

Source: Illusie--Laszlo--Orgogozo, Exposé VI, 1.4 and 1.6(i)--(ii),
printed pp. 69--70 (blueprint: lem-trf-complete-toric-monomial-factors).
-/

@[expose] public section

universe u v

open AlgebraicGeometry AddMonoidAlgebra

/-- Every factor of a chart monomial in either complete toric local model is a unit
 times a chart monomial.
Source: Illusie--Laszlo--Orgogozo, Exposé VI, 1.4 and 1.6(i)--(ii),
printed pp. 69--70 (blueprint: lem-trf-complete-toric-monomial-factors).

Proof: In each coefficient model, localize at the multiplicative set of all chart
monomials.  If `b * c` is the chart monomial indexed by `q`, then the image of `b`
has inverse the image of `c` divided by that monomial, so it is a unit in the
localization.  The complete-local divisorial recognition equality from
`lem-trf-complete-toric-kato-recognition` therefore writes `b` as a ring unit times
a chart monomial.  Conversely, the displayed factorization is exactly the required
factor of the original monomial.  The same argument includes `q = 0`, the trivial
monoid, and `n = 0`.
(blueprint: lem-trf-complete-toric-monomial-factors). -/
theorem complete_toric_monomial_factor
    (P : Type u) [AddCommMonoid P]
    (hP : IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ q : P, IsAddUnit q → q = 0) (n : ℕ) :
    (∀ (k : Type v) [Field k] (q : P)
      (b c : CompletedLocalModel k P n),
      b * c = completeToricChart k P n ((q : Multiplicative P)) →
        ∃ (r : P) (u : (CompletedLocalModel k P n)ˣ),
          b = (u : CompletedLocalModel k P n) *
            completeToricChart k P n ((r : Multiplicative P))) ∧
    (∀ (C : Type v) [CommRing C] [IsLocalRing C] (p : ℕ), IsCohenRing p C →
      ∀ (θ : CompletedLocalModel C P n),
        θ - (p : CompletedLocalModel C P n) ∈ completedLocalModelBoundaryIdeal C P n →
        ∀ (q : P) (b c : cohenCompleteToricRing C P n θ),
          b * c = cohenCompleteToricChart C P n θ ((q : Multiplicative P)) →
            ∃ (r : P) (u : (cohenCompleteToricRing C P n θ)ˣ),
              b = (u : cohenCompleteToricRing C P n θ) *
                cohenCompleteToricChart C P n θ ((r : Multiplicative P))) := by
  sorry
