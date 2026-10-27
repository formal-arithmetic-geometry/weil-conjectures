module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Weighted Taylor coefficient spaces

Source: Frenkel, Séminaire H. Cartan 1951–52, exposé 10, §4, pp. 6–7;
the weighted summable coefficient formulation is agent supplied
(blueprint: def-sfb-weighted-taylor-coefficients).
-/

@[expose] public section

set_option autoImplicit false

namespace Complex.Taylor

/-- Positive polyradii, including the unique empty polyradius in dimension zero.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def Polyradius (d : ℕ) := {ρ : Fin d → ℝ // ∀ i, 0 < ρ i}

/-- The positive monomial weight of a multiindex.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def weight {d : ℕ} (ρ : Polyradius d) (α : Fin d →₀ ℕ) : ℝ :=
  ∏ i, ρ.val i ^ α i

/-- The weighted absolutely summable coefficient families. Formal-series multiplication
is convolution, not pointwise multiplication.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def CoefficientSpace {d : ℕ} (ρ : Polyradius d) :=
  {c : MvPowerSeries (Fin d) ℂ // Summable (fun α ↦ ‖c α‖ * weight ρ α)}

/-- The specified weighted sum norm; its norm laws are conclusions of the Banach model.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
noncomputable def coefficientNorm {d : ℕ} (ρ : Polyradius d) (c : CoefficientSpace ρ) : ℝ :=
  ∑' α, ‖c.val α‖ * weight ρ α

/-- The scalar monomial, with empty product equal to one.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def monomialValue {d : ℕ} (α : Fin d →₀ ℕ) (z : Fin d → ℂ) : ℂ :=
  ∏ i, z i ^ α i

/-- The series sum as a total function. Summability on the polydisc is asserted separately.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
noncomputable def seriesValue {d : ℕ} {ρ : Polyradius d} (c : CoefficientSpace ρ)
    (z : Fin d → ℂ) : ℂ :=
  ∑' α, c.val α * monomialValue α z

/-- The open polydisc of a positive polyradius.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def polydisc {d : ℕ} (ρ : Polyradius d) : Set (Fin d → ℂ) :=
  {z | ∀ i, ‖z i‖ < ρ.val i}

/-- The retained radii on a coordinate subspace.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def coordinateRadius {d k : ℕ} (e : Fin k ↪ Fin d) (ρ : Polyradius d) : Polyradius k :=
  ⟨fun j ↦ ρ.val (e j), fun j ↦ ρ.property (e j)⟩

/-- Coordinate inclusion: fill every coordinate outside the image of `e` with zero.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-weighted-taylor-coefficients). -/
def coordinateInclusion {d k : ℕ} (e : Fin k ↪ Fin d) (z : Fin k → ℂ) : Fin d → ℂ :=
  fun i ↦ ∑ j, if e j = i then z j else 0

end Complex.Taylor
