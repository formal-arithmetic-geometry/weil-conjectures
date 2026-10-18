/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.OpenComplementCondition
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Finite affine chart covers used in the purity admissibility statement

Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
thm-pur-general-admissibility, affine chart paragraph
(blueprint: def-pur-affine-chart-cover).

## Main definitions

- `PurityAffineChartCover`: the finite covers, closed presentations and complements.
- `PurityAffineChartCover.maxEmbeddingDimension`: the maximum dimension D.
- `PurityAffineChartCover.preservationConstant`: the chart-bound maximum c.
- `PurityAffineChartCover.openComplementConditions`: the etale complement conditions.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- A finite affine base cover, finite affine covers upstairs, and closed presentations
in relative affine spaces, with their open complements. Charts may be empty.
Source: blueprint thm-pur-general-admissibility, affine chart paragraph
(blueprint: def-pur-affine-chart-cover). -/
structure PurityAffineChartCover {X Y : Scheme.{u}} (f : X ⟶ Y) where
  baseCount : ℕ
  baseOpen : Fin baseCount → Y.Opens
  base_affine : ∀ v, IsAffineOpen (baseOpen v)
  base_cover : ∀ y : Y, ∃ v, y ∈ baseOpen v
  chartCount : Fin baseCount → ℕ
  chartOpen : (v : Fin baseCount) → Fin (chartCount v) → X.Opens
  chart_affine : ∀ v i, IsAffineOpen (chartOpen v i)
  chart_contained : ∀ v i, chartOpen v i ≤ f ⁻¹ᵁ baseOpen v
  chart_cover : ∀ v (x : X), f x ∈ baseOpen v → ∃ i, x ∈ chartOpen v i
  embeddingDimension : (v : Fin baseCount) → Fin (chartCount v) → ℕ
  embedding : ∀ v i, (chartOpen v i).toScheme ⟶
    AffineSpace (ULift.{u} (Fin (embeddingDimension v i))) (baseOpen v).toScheme
  embedding_closed : ∀ v i, IsClosedImmersion (embedding v i)
  embedding_over : ∀ v i,
    embedding v i ≫ (AffineSpace (ULift.{u} (Fin (embeddingDimension v i)))
      (baseOpen v).toScheme ↘ (baseOpen v).toScheme) ≫ (baseOpen v).ι =
        (chartOpen v i).ι ≫ f
  complement : ∀ v i,
    (AffineSpace (ULift.{u} (Fin (embeddingDimension v i))) (baseOpen v).toScheme).Opens
  complement_eq : ∀ v i, (complement v i : Set _) = (Set.range (embedding v i))ᶜ
  complement_quasiCompact : ∀ v i, QuasiCompact (complement v i).ι

/-- The maximum of the chart dimensions, with value zero for no charts.
Source: blueprint thm-pur-general-admissibility, definition of D
(blueprint: def-pur-affine-chart-cover). -/
def PurityAffineChartCover.maxEmbeddingDimension {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : PurityAffineChartCover f) : ℕ :=
  Finset.univ.sup fun i : (v : Fin C.baseCount) × Fin (C.chartCount v) ↦
    C.embeddingDimension i.1 i.2

/-- The maximum of c_U + 1 + 2(D - d_U), with value zero for no charts.
Each d_U is bounded by D, so natural subtraction agrees with integer subtraction.
Source: blueprint thm-pur-general-admissibility, definition of c
(blueprint: def-pur-affine-chart-cover). -/
def PurityAffineChartCover.preservationConstant {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : PurityAffineChartCover f)
    (cU : (v : Fin C.baseCount) → Fin (C.chartCount v) → ℕ) : ℕ :=
  Finset.univ.sup fun i : (v : Fin C.baseCount) × Fin (C.chartCount v) ↦
    cU i.1 i.2 + 1 + 2 *
      (C.maxEmbeddingDimension - C.embeddingDimension i.1 i.2)

/-- The recorded two-clause open-complement condition for each chart complement.
Source: blueprint thm-pur-general-admissibility, open-complement hypothesis
(blueprint: def-pur-affine-chart-cover). -/
def PurityAffineChartCover.openComplementConditions {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : PurityAffineChartCover f) (A : Type (u + 1)) [CommRing A] [Finite A]
    (cU : (v : Fin C.baseCount) → Fin (C.chartCount v) → ℕ) : Prop :=
  ∀ v i, @HasOpenComplementCondition A _ _ _ _
    (C.complement v i).ι inferInstance (C.complement_quasiCompact v i) (cU v i)

end AlgebraicGeometry.Scheme
