/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Gauss completeness and last-variable regrouping of restricted series

Source: the explicit coefficient argument in the DAG, steps 1--7
(blueprint: lem-trf-restricted-series-gauss-completion). The descriptive reference
is Bosch--Guentzer--Remmert, Non-Archimedean Analysis, basic Gauss-norm properties;
the book is not available locally and no theorem or page number has been verified.
The proof is the agent-written argument recorded by Q42, not a quotation from BGR.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- Restricted series over a complete nonarchimedean field are complete for the
Gauss metric; total-degree truncations converge, and regrouping by the last
variable is an isometric ring identification with restricted series in that variable.
The metrics are existentially quantified and fixed by their distance formula, so no
coefficientwise topology is substituted. The target subring is fixed by the exact
row-norm decay predicate, and the equivalence by its individual coefficients.

Source: the agent-written coefficient proof, steps 1--7, in the DAG
(blueprint: lem-trf-restricted-series-gauss-completion). BGR, Non-Archimedean Analysis,
is a descriptive reference only, unavailable locally; no page number is asserted.

Proof plan:
1. The finite set of coefficients of norm at least one bounds all coefficients.
   Hence the Gauss supremum is finite, separates zero, sends one to one and is
   invariant under negation. The coefficientwise ultrametric inequality gives the
   maximum bound for addition and the triangle inequality for the Gauss distance.
2. Each Cauchy-product coefficient is a finite sum indexed by an antidiagonal.
   Its norm is at most the product of the two Gauss norms. For restrictedness,
   take M=max(1, norm f, norm g): an epsilon-large coefficient can only occur in
   the sum of the finite epsilon/M-exceptional sets of the factors. These are
   the inherited subring operations of def-trf-restricted-series-presentation.
3. Regard the multi-indices as a discrete space. A Gauss-Cauchy sequence is a
   Cauchy sequence of bounded continuous coefficient functions for the same sup
   distance. Apply lem-trf-bounded-families-complete, namely Mathlib's
   BoundedContinuousFunction.instCompleteSpace, to obtain a uniform coefficient limit.
4. Approximate the limit uniformly within epsilon/2 by one restricted series.
   Outside that series' finite epsilon/2-exceptional set, the ultrametric
   inequality bounds the limit coefficient by a number smaller than epsilon.
   Thus the limit is restricted, proving completeness for the specified metric.
5. Bound the total degrees of the finite epsilon/2-exceptional set. All omitted
   coefficients of every later truncation have norm below epsilon/2, so their
   supremum is at most epsilon/2. The total-degree cutoff is finite because each
   coordinate is bounded by the cutoff. This proves convergence of truncations.
6. Slice the coefficient family along the last variable. Every row is restricted.
   Project the finite epsilon/2-exceptional set onto the last coordinate to see
   that the row Gauss norms tend to zero. Conversely only finitely many rows can
   contain an epsilon-large coefficient, and each contains finitely many. This
   gives inverse coefficient assignments. The supremum over pairs equals the
   iterated supremum, proving preservation of norms and distances.
7. Addition is coefficientwise. For multiplication both coefficient expressions
   are the same finite double antidiagonal sum, so regrouping is a ring map.
   Constants have only their zero multi-index coefficient; multiplication by the
   last variable shifts the last exponent by one. These formulas prove the two
   compatibilities. For zero variables the multi-index set is a singleton, so
   the constants map is a bijective isometry from F. All arguments include s=0.
-/
theorem restricted_series_gauss_completion
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F] :
    (∀ (n : ℕ)
      (f : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ)))),
      MvPowerSeries.HasGaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) f.val ∧
      (MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) f.val = 0 ↔ f = 0) ∧
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) (-f).val =
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) f.val) ∧
    (∀ n : ℕ,
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) 1 = 1) ∧
    (∀ (n : ℕ)
      (f g : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ)))),
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) (f + g).val ≤
        max (MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) f.val)
          (MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) g.val) ∧
      MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) (f * g).val ≤
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) f.val *
          MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) g.val) ∧
    ∃ M : ∀ n : ℕ, MetricSpace
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))),
      (∀ (n : ℕ)
        (f g : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ)))),
        @dist _ (M n).toDist f g =
          MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) (f - g).val) ∧
      (∀ n : ℕ, @CompleteSpace _ (M n).toUniformSpace) ∧
      (∀ (n : ℕ)
        (f : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ)))),
        ∃ p : ℕ →
            ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))),
          (∀ N : ℕ, (p N).val =
            (MvPowerSeries.truncTotal (N + 1) f.val).toMvPowerSeries) ∧
          Filter.Tendsto p Filter.atTop (@nhds _ (M n).toUniformSpace.toTopologicalSpace f)) ∧
      Function.Bijective (constants F 0) ∧
      (∀ a : F,
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin 0 ↦ 1)
          (constants F 0 a).val = ‖a‖) ∧
      ∀ s : ℕ,
        ∃ S : Subring (PowerSeries
            ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin s ↦ (1 : ℝ)))),
          (∀ a : PowerSeries
              ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin s ↦ (1 : ℝ))),
            a ∈ S ↔ Filter.Tendsto
              (fun i : ℕ ↦ MvPowerSeries.gaussNorm (norm : F → ℝ)
                (fun _ : Fin s ↦ 1) (PowerSeries.coeff i a).val)
              Filter.atTop (nhds 0)) ∧
          ∃ e : ↥(MvPowerSeries.IsRestricted.subring (R := F)
                (fun _ : Fin (s + 1) ↦ (1 : ℝ))) ≃+* S,
            (∀ (f : ↥(MvPowerSeries.IsRestricted.subring (R := F)
                  (fun _ : Fin (s + 1) ↦ (1 : ℝ)))) (i : ℕ) (μ : Fin s →₀ ℕ),
              MvPowerSeries.coeff μ (PowerSeries.coeff i (e f).val).val =
                MvPowerSeries.coeff
                  (Finsupp.equivFunOnFinite.symm (Fin.snoc (fun j ↦ μ j) i)) f.val) ∧
            (∀ f,
              MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin (s + 1) ↦ 1) f.val =
                ⨆ i : ℕ, MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin s ↦ 1)
                  (PowerSeries.coeff i (e f).val).val) ∧
            (∀ f g,
              @dist _ (M (s + 1)).toDist f g =
                ⨆ i : ℕ, MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin s ↦ 1)
                  (PowerSeries.coeff i ((e f).val - (e g).val)).val) ∧
            (∀ a : F, (e (constants F (s + 1) a)).val =
              PowerSeries.C (constants F s a)) ∧
            ∀ f,
              (e (⟨MvPowerSeries.X (Fin.last s),
                MvPowerSeries.isRestricted_monomial _ _ _⟩ * f)).val =
                  PowerSeries.X * (e f).val := by
  sorry

end RestrictedSeries
