/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.RingTheory.Trace.Basic

/-!
# Coordinate bounds for the spectral norm in characteristic zero

Source: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Proposition 3.5.1/4 and
Definition 3.5.2/1, printed pp. 152–153
(blueprint: lem-trf-char-zero-spectral-coordinate-topology).

The norm on a finite family of coefficients is the maximum of their absolute values.
The base field need not be complete.
-/

@[expose] public section

universe u v w

namespace Module.Basis

/-- Over a characteristic-zero nonarchimedean nontrivially normed field, the
minimal-polynomial spectral norm of a finite extension has two-sided coordinate bounds
for every basis. Source: Bosch–Güntzer–Remmert, Non-Archimedean Analysis,
Proposition 3.5.1/4 and Definition 3.5.2/1, printed pp. 152–153
(blueprint: lem-trf-char-zero-spectral-coordinate-topology).

Proof: write `s = spectralNorm K L` and `z = ∑ i, a i • b i`.
By `lem-trf-incomplete-spectral-algebra-norm`, scalar homogeneity and the ultrametric
triangle inequality give `s z ≤ C * ‖a‖`, where `C = max i, s (b i) > 0`.
For any `u : L`, the defining coefficient maximum gives `‖(minpoly K u).nextCoeff‖ ≤ s u`.
By `lem-trf-field-trace-minpoly-coefficient`, its trace is a natural-number multiple
of the negative of that coefficient. Ultrametricity gives `‖(n : K)‖ ≤ 1` by induction,
so `‖Algebra.trace K L u‖ ≤ s u`, also when `u = 0`.
By `lem-trf-char-zero-trace-dual-basis`, characteristic zero supplies a trace-dual
basis `w`, and trace linearity gives `Algebra.trace K L (z * w j) = a j`.
The trace bound and spectral submultiplicativity yield `‖a j‖ ≤ s z * s (w j)`.
Take the maximum over `j` and put `B = max j, s (w j) > 0`; then `c = B⁻¹`
gives the lower bound. The bases are nonempty because `L` is a field, and their
vectors are nonzero, proving positivity of both maxima. No step uses completeness. -/
theorem spectralNorm_coordinate_bounds
    {K : Type u} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
    {L : Type v} [Field L] [Algebra K L] [FiniteDimensional K L]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι K L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ι → K,
      c * ‖a‖ ≤ spectralNorm K L (∑ i, a i • b i) ∧
        spectralNorm K L (∑ i, a i • b i) ≤ C * ‖a‖ := by
  sorry

end Module.Basis
