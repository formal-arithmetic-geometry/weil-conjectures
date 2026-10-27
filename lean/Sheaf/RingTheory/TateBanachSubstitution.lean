/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Contractive substitution in restricted power series

Source: Conrad, Several approaches to non-archimedean geometry, Exercise 1.2.8(3),
PDF p. 7, the norm-at-most-one case
(blueprint: lem-per-tate-banach-substitution).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- A bounded tuple defines a unique continuous scalar-compatible ring homomorphism
from restricted series, given by the net of finite partial sums, and this map is
contractive. Scalar compatibility is precisely the algebra-homomorphism condition.
Continuity is written in epsilon--delta form for the Gauss metric on the source;
`HasSum` uses the net over all finite subsets of multi-indices. When there are no
variables, the map takes a series to the scalar image of its constant coefficient.
Source: Conrad, Several approaches to non-archimedean geometry, Exercise 1.2.8(3),
PDF p. 7 (blueprint: lem-per-tate-banach-substitution).

Proof (the node's six steps):
1. Apply lem-trf-restricted-series-gauss-completion: the Gauss norm is finite and
   separated, ultrametric and submultiplicative, and total-degree truncations converge.
   Its coefficient formula gives scalar homogeneity, including at zero. Consequently
   the polynomial subspace is dense in the restricted-series normed vector space.
2. Evaluate polynomials by finite sums at the bounded tuple. Submultiplicativity
   bounds each monomial by one; induction using the ultrametric inequality bounds
   evaluation by the Gauss norm. Finite distributivity proves multiplicativity and
   the constant and variable identities. Evaluation is a linear contraction.
3. Apply lem-sfb-dense-subspace-contractive-extension, namely LinearMap.extendOfNorm,
   to the polynomial inclusion and evaluation. This gives a continuous linear
   contraction on restricted series agreeing with polynomial evaluation.
4. If p_N and q_N are truncations of f and g, submultiplicativity bounds the error
   p_N*q_N-f*g by max(norm(f)*norm(q_N-g), norm(p_N-f)*norm(g)), which tends to zero.
   The analogous target estimate and contractivity show that the extension preserves
   multiplication. It preserves one and scalars by agreement on polynomials.
5. Given epsilon > 0, restrictedness makes the indices with coefficient norm at least
   epsilon/2 finite. Every partial sum containing them differs from f by Gauss norm
   at most epsilon/2. Contractivity therefore identifies the full partial-sum net's
   limit with the extension's value.
6. Any continuous scalar-compatible ring map with the same variable images agrees
   on polynomials. Continuity and density give equality on every series. For r = 0
   the multi-index set is a singleton and its monomial is the empty product one,
   so the partial sums are eventually the scalar image of the constant coefficient. -/
theorem exists_contractive_substitution
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (B : Type v) [NormedCommRing B] [NormOneClass B] [IsUltrametricDist B]
    [NormedAlgebra F B] [CompleteSpace B]
    (r : ℕ) (b : Fin r → B) (hb : ∀ i : Fin r, ‖b i‖ ≤ 1) :
    ∃ φ : (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) →+* B,
      φ.comp (constants F r) = algebraMap F B ∧
      (∀ f ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ g,
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin r ↦ 1)
          (g.val - f.val) < δ → ‖φ g - φ f‖ < ε) ∧
      (∀ i : Fin r, φ ⟨MvPowerSeries.X i,
        MvPowerSeries.isRestricted_monomial _ (Finsupp.single i 1) (1 : F)⟩ = b i) ∧
      (∀ f, HasSum (fun ν : Fin r →₀ ℕ ↦
        algebraMap F B (MvPowerSeries.coeff ν f.val) * ν.prod (fun i n ↦ b i ^ n))
        (φ f)) ∧
      (∀ f, ‖φ f‖ ≤ MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin r ↦ 1) f.val) ∧
      (∀ ψ : (MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) →+* B,
        ψ.comp (constants F r) = algebraMap F B →
        (∀ f ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ g,
          MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin r ↦ 1)
            (g.val - f.val) < δ → ‖ψ g - ψ f‖ < ε) →
        (∀ i : Fin r, ψ ⟨MvPowerSeries.X i,
          MvPowerSeries.isRestricted_monomial _ (Finsupp.single i 1) (1 : F)⟩ = b i) →
        ψ = φ) ∧
      (r = 0 → ∀ f, φ f = algebraMap F B (MvPowerSeries.constantCoeff f.val)) := by
  sorry

end RestrictedSeries
