/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Diagonal
public import WeilConjectures.RingTheory.Etale.DepthTwo.Global
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPuritySpread

/-!
# Purity for normal covers of a smooth algebra over a normal base

Let `R₀` be a Noetherian integrally closed domain, `q ≠ 0` a prime of `R₀`, `B` a smooth
`R₀`-algebra, `M` a `B`-algebra in which the nonzero elements of `R₀` are invertible
(geometrically: a cover of the generic fibre) and `T` the integral closure of `B` in `M`. Let `P`
be a prime of `B` over `q`. If `T` is finite étale near every prime `Q ⊆ P` of `B` which does not
lie over `q`, and near the minimal primes of `qB` contained in `P` (the generic points of the
components of the fibre), then `T` is finite étale near `P`
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`).

The proof is an induction on the primes between the minimal primes of `qB` and `P`. At `P`, with
`O = B_P` (a normal domain, being smooth over the normal `(R₀)_q`), `T_P` is finite over `O` and
étale over `D(a) ∪ D(β)` for `0 ≠ a ∈ q` and a suitable `β ∈ P` such that `(a, β)` is a regular
pair on `T_P`; the diagonal local ring `R = (B ⊗_{R₀} B)_{Δ(P)}` with its two projections and the
swap involution satisfies the hypotheses of `RingTheory.DepthTwo.etale_of_diagonal`, whose prime
`Q` comes from the generic point of the fibre of the second projection through `Δ(P)`. The
induction is on the height of `P`; the step at `P` is
`RingTheory.DepthTwo.etale_finite_localization_of_smooth` (finite étaleness of `T_P`) followed by
`RingTheory.DepthTwo.exists_etale_finite_away_of_localization` (spreading out to `D(h)`).

This is the commutative algebra of purity for normal covers of a scheme smooth over a normal
Noetherian base (`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`,
[Stacks 0EYE] and [Stacks 0EYB] in the form used in [Stacks 0EYJ]), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace RingTheory.DepthTwo

variable {R₀ B M : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing M] [Algebra B M] [Algebra R₀ M] [IsScalarTower R₀ B M]

/-- **Purity for normal covers of a smooth algebra over a normal base.** See the module
docstring. -/
theorem exists_etale_integralClosure_of_smooth (q : Ideal R₀) [q.IsPrime] (hq : q ≠ ⊥)
    (hunit : ∀ r : R₀, r ≠ 0 → IsUnit (algebraMap R₀ M r)) (P : Ideal B) [P.IsPrime]
    (hP : P.comap (algebraMap R₀ B) = q)
    (H : ∀ Q : Ideal B, Q.IsPrime → Q ≤ P →
      (Q.comap (algebraMap R₀ B) ≠ q ∨ Q ∈ (q.map (algebraMap R₀ B)).minimalPrimes) →
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M)) :
    ∃ h ∉ P, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ B
  -- induction on the height of the primes `P' ⊆ P` over `q`
  have key (n : ℕ) : ∀ P' : Ideal B, P'.IsPrime → P' ≤ P → P'.comap (algebraMap R₀ B) = q →
      P'.height = n → ∃ h ∉ P', Algebra.Etale (Localization.Away h)
        (Localization.Away h ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P' hP' hP'P hP'q hn
      by_cases hmin : P' ∈ (q.map (algebraMap R₀ B)).minimalPrimes
      · exact H P' hP' hP'P (Or.inr hmin)
      have H' (Q : Ideal B) (hQ : Q.IsPrime) (hQP' : Q < P') : ∃ h ∉ Q, Algebra.Etale
          (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
          Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) := by
        by_cases hQq : Q.comap (algebraMap R₀ B) = q
        · have hm : ((Q.height.toNat : ℕ) : ℕ∞) = Q.height :=
            ENat.natCast_toNat Ideal.height_ne_top_of_isPrime
          have hlt : Q.height < P'.height := Ideal.height_strict_mono_of_isPrime hQP'
          rw [hn, ← hm, Nat.cast_lt] at hlt
          exact ih _ hlt Q hQ (hQP'.le.trans hP'P) hQq hm.symm
        · exact H Q hQ (hQP'.le.trans hP'P) (Or.inl hQq)
      obtain ⟨hE, hF⟩ := etale_finite_localization_of_smooth q hq hunit P' hP'q.symm hmin H'
      exact exists_etale_finite_away_of_localization hunit P' (by rwa [hP'q]) H'
  exact key _ P inferInstance le_rfl hP (ENat.natCast_toNat Ideal.height_ne_top_of_isPrime).symm

end RingTheory.DepthTwo
