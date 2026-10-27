/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Best approximation in finite-dimensional ultrametric subspaces

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent analytic auxiliary for the geometric norm projection;
an exact external reference is WANTED
(blueprint: lem-sfb-finite-ultrametric-best-approximation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

/-- A finite-dimensional subspace of an ultrametric normed space over a finite p-adic
extension contains a nearest point to every vector. The distance is positive outside
that subspace, without completeness of the ambient vector space.

Source: main-20261015 blueprint, `sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), agent analytic auxiliary; exact external reference WANTED
(blueprint: lem-sfb-finite-ultrametric-best-approximation).

Proof: Equip `E` with its recorded extending absolute value. By
`lem-weil-l-adic-extension-proper`, it is proper, hence locally compact; its absolute
value is nontrivial since the norm of `l` is `l` inverse, less than one. The homogeneous
norm restricted to `W` gives a normed space. Apply
`lem-sfb-finite-dimensional-normed-proper` (`FiniteDimensional.proper`) to see that
`C = {w : W | ‖w‖ ≤ ‖x‖}` is compact. It contains zero, including when `x = 0` or `W = 0`.
The function `f(w) = ‖x - w‖` is 1-Lipschitz by the ordinary triangle inequality,
so continuous. By `lem-sfb-compact-real-function-minimum`
(`IsCompact.exists_isMinOn`), it attains its minimum at some `w₀` in `C`.
Comparing with zero gives `f(w₀) ≤ ‖x‖`.

If `w` lies outside `C`, then `‖w‖ > ‖x‖`. Ultrametricity gives both
`f(w) ≤ max ‖x‖ ‖w‖ = ‖w‖` and `‖w‖ ≤ max ‖x‖ (f(w))`, by writing
`w = x - (x - w)`. Thus `f(w) = ‖w‖ > ‖x‖ ≥ f(w₀)`. Consequently `w₀` minimizes
`f` over all of `W`. Its value equals the infimum of the nonempty set of distances,
which is bounded below by zero. If `x ∉ W`, then `x - w₀ ≠ 0`, so definiteness
makes this minimum strictly positive. No completeness of `V` was used.
-/
theorem exists_finite_ultrametric_best_approximation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (V : Type v) [NormedAddCommGroup V] [Module E V]
    (h_hom : ∀ (a : E) (v : V),
      ‖a • v‖ = coefficientExtensionAbsoluteValue l E a * ‖v‖)
    (h_ultra : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖)
    (W : Submodule E V) [FiniteDimensional E W] (x : V) :
    (∃ w₀ : W, ‖x - (w₀ : V)‖ = ⨅ w : W, ‖x - (w : V)‖) ∧
      (x ∉ W → 0 < ⨅ w : W, ‖x - (w : V)‖) := by
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic l) E
  let : NormedSpace (Padic l) E := spectralNorm.normedSpace (Padic l) E
  have : ProperSpace E := FiniteDimensional.proper (Padic l) E
  let : NormedSpace E V :=
    { norm_smul_le := fun a v ↦ le_of_eq (h_hom a v) }
  have : ProperSpace W := FiniteDimensional.proper E W
  have hzero : (0 : W) ∈ Metric.closedBall (0 : W) ‖x‖ := by
    simp [norm_nonneg]
  have hcont : Continuous (fun w : W ↦ ‖x - (w : V)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_closedBall (0 : W) ‖x‖).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  have hbound : ‖x - (w₀ : V)‖ ≤ ‖x‖ := by
    simpa using hmin hzero
  have hglobal (w : W) : ‖x - (w₀ : V)‖ ≤ ‖x - (w : V)‖ := by
    by_cases hw : w ∈ Metric.closedBall (0 : W) ‖x‖
    · exact hmin hw
    · have hlarge : ‖x‖ < ‖(w : V)‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm, not_le] using hw
      have htri := h_ultra x (-(x - (w : V)))
      rw [show x + -(x - (w : V)) = (w : V) by abel, norm_neg] at htri
      have hwle : ‖(w : V)‖ ≤ ‖x - (w : V)‖ :=
        (le_max_iff.mp htri).resolve_left (not_le.mpr hlarge)
      exact hbound.trans (hlarge.le.trans hwle)
  have heq : ‖x - (w₀ : V)‖ = ⨅ w : W, ‖x - (w : V)‖ := by
    apply le_antisymm
    · exact le_ciInf hglobal
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ w₀
  refine ⟨⟨w₀, heq⟩, fun hx ↦ ?_⟩
  rw [← heq]
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h ↦ hx (h ▸ w₀.property)))

end Padic
