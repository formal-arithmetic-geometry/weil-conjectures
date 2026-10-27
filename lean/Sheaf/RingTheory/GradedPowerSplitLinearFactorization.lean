module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Uniform linear factorization for power-split differentials

Source: Stacks Project, Local Cohomology, Tags 0GA6, 0GAC and the finite-sum
composition in 0GAD (blueprint: lem-per-graded-power-split-linear-factorization).

An ideal image `(K ^ a).map (Ideal.Quotient.mk (K ^ b))` represents
`K^a / K^b` when `a ≤ b`. Maps to these modules are written after restricting
scalars to `R`; since the modules are annihilated by `K^n`, these are exactly
the maps linear over `R / K^n`. The reduction equation is stated on all ring
representatives, specifying the canonical map without a choice of lifts.
-/

@[expose] public section

universe u₀ u v

namespace Ideal

/-- Uniform factorization after bounded loss of adic precision, with no completeness
hypothesis. Source: Stacks Project, Local Cohomology, Tags 0GA6 and 0GAC, composed
with the scalar splittings as in 0GAD
(blueprint: lem-per-graded-power-split-linear-factorization).

Proof: apply `lem-per-graded-near-projective-hom-divisibility` to obtain `D,q`.
Set `e = (D+2)c` and `N = max (q+e) (2e+1)`. These bounds imply all the cited
lemma's inequalities, including `n ≥ q+2c` if `D=0`. The fixed maps `d,h_a`
supply its finite-free factorizations, and finite generation over `R/K^n`
implies finite generation over `R`. Put `t = n-(D+1)c` and `s = n-e`, so
`t = s+c`. The cited lemma gives `p u = ∑ a_j ψ_j` with `a_j ∈ K^c` and
`ψ_j : M → K^s/K^(n+s)`. Define `V = ∑ ψ_j h_(a_j)`. Then
`V d = ∑ a_j ψ_j`, regarded in `K^s/K^(n+s)` by the inclusion from degree `t`.
Reduce this map modulo `K^(2s)` to obtain `v`. Checking representatives gives
`v d = ρ u`. All maps respect the quotient-ring action since
`K^n K^s = K^(n+s) ⊆ K^(2s)`. No completion is used. -/
theorem exists_graded_power_split_linear_factorization
    (R₀ : Type u₀) [CommRing R₀] [IsNoetherianRing R₀]
    (K₀ : Ideal R₀) (c : ℕ) :
    ∃ e N : ℕ, 2 * e + 1 ≤ N ∧
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Ideal R)
        (E : associatedGraded K ≃+* associatedGraded K₀),
        (∀ j : ℕ,
          E '' Set.range (DirectSum.of (associatedGradedPiece K) j) =
            Set.range (DirectSum.of (associatedGradedPiece K₀) j)) →
        ∀ (n : ℕ), N ≤ n →
        ∀ (M : ModuleCat.{v} (R ⧸ K ^ n)) [Module.Finite (R ⧸ K ^ n) M]
          (r : ℕ) (d : M →ₗ[R ⧸ K ^ n] (Fin r → R ⧸ K ^ n)),
          (∀ a : (K ^ c : Ideal R),
            ∃ h : (Fin r → R ⧸ K ^ n) →ₗ[R ⧸ K ^ n] M,
              h.comp d = Ideal.Quotient.mk (K ^ n) (a : R) • LinearMap.id) →
          ∀ u : (ModuleCat.restrictScalars (Ideal.Quotient.mk (K ^ n))).obj M →ₗ[R]
              (K ^ n).map (Ideal.Quotient.mk (K ^ (2 * n))),
            ∃ v : (Fin r → R ⧸ K ^ n) →ₗ[R]
                (K ^ (n - e)).map (Ideal.Quotient.mk (K ^ (2 * (n - e)))),
              ∀ (x : M) (y : R),
                Ideal.Quotient.mk (K ^ (2 * n)) y = (u x).val →
                Ideal.Quotient.mk (K ^ (2 * (n - e))) y = (v (d x)).val := by
  sorry

end Ideal
