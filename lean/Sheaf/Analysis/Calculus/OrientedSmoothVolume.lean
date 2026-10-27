module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Positive smooth volume data

Source: Demailly, Complex Analytic and Differential Geometry, VI §1, before (1.4)
(blueprint: def-sfb-oriented-smooth-volume).

A positive volume form is represented by its positive smooth densities in an oriented
smooth atlas and its associated Borel measure. Positive transition determinants encode
the orientation. The measure equality is the coordinate meaning of integration against
the volume form; it also enforces compatibility of the densities on overlaps.
-/

@[expose] public section

universe u

open MeasureTheory
open scoped ContDiff

namespace Manifold

/-- An oriented smooth atlas and a positive smooth volume form, in coordinate-density
representation. Source: Demailly VI §1, before (1.4)
(blueprint: def-sfb-oriented-smooth-volume). -/
structure OrientedSmoothVolume {m : ℕ} (M : Type u) [TopologicalSpace M]
    [ChartedSpace (Fin m → ℝ) M] [MeasurableSpace M] where
  /-- A covering atlas of positively oriented coordinate charts. -/
  charts : Set (OpenPartialHomeomorph M (Fin m → ℝ))
  /-- The charts belong to the given smooth structure. -/
  smooth_charts : charts ⊆ IsManifold.maximalAtlas (𝓘(ℝ, Fin m → ℝ)) ∞ M
  /-- No points of the manifold are omitted. -/
  covers : ∀ x : M, ∃ c ∈ charts, x ∈ c.source
  /-- Coordinate changes preserve orientation. -/
  positive_transition : ∀ c ∈ charts, ∀ e ∈ charts, ∀ x ∈ c.source ∩ e.source,
    0 < LinearMap.det (fderiv ℝ (e ∘ c.symm) (c x)).toLinearMap
  /-- The measure used for volume integrals. -/
  measure : Measure M
  /-- Coordinate densities, with arbitrary values outside the chart targets. -/
  density : OpenPartialHomeomorph M (Fin m → ℝ) → (Fin m → ℝ) → ℝ
  /-- Smoothness of each density on its coordinate domain. -/
  smooth_density : ∀ c ∈ charts, ContDiffOn ℝ ∞ (density c) c.target
  /-- Positivity of the volume form. -/
  positive_density : ∀ c ∈ charts, ∀ y ∈ c.target, 0 < density c y
  /-- The local definition of the measure associated to the volume form. -/
  map_measure : ∀ c ∈ charts,
    Measure.map c (measure.restrict c.source) =
      (volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (density c y))

end Manifold
