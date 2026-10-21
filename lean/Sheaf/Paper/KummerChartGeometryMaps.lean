/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerConstantNerveTerm
public import Sheaf.Paper.KummerParameterizedTerm
public import Sheaf.Paper.KummerStratumGeometry

/-! # Canonical maps attached to one full-root chart
Source: direct-image proof (3), actual root chart and its punctured covering.
(blueprint: def-sfb-kummer-chart-geometry-maps).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar
variable {Y : Scheme.{u}} {A : Type u} [Finite A]
  {C : A → Y.IdealSheafData} {I : Finset A}

/-- The actual local open immersion in the published full-root chart.
Source: direct-image proof (3), U_alpha^circ
(blueprint: def-sfb-kummer-chart-geometry-maps). -/
def kummerChartOpen (D : Y.IdealSheafData) (c : TameRootExtensionChart C I) :
    c.puncturedBase D ⟶ c.U :=
  pullback.fst c.toBase (tameBoundaryOpen D).ι

/-- The actual restriction map from the chart open to the original open.
Source: direct-image proof (3), local coefficient pullback
(blueprint: def-sfb-kummer-chart-geometry-maps). -/
def kummerChartToOpen (D : Y.IdealSheafData) (c : TameRootExtensionChart C I) :
    c.puncturedBase D ⟶ (tameBoundaryOpen D).toScheme :=
  pullback.snd c.toBase (tameBoundaryOpen D).ι

/-- Puncturing and then mapping to the local base is the actual local covering map.
Source: direct-image proof (3), root-nerve base
(blueprint: def-sfb-kummer-chart-geometry-maps).
Proof: expand the pullback projections defining toPuncturedBase. Its first
projection is openInclusion followed by towerMap. -/
theorem kummerChartOpen_commutes (p : ℕ) (D : Y.IdealSheafData)
    (c : TameRootExtensionChart C I) :
    c.openInclusion p D ≫ c.towerMap p =
      c.toPuncturedBase p D ≫ kummerChartOpen D c := by
  sorry

/-- The punctured coefficient pullback agrees with the original restriction to W.
Source: direct-image proof (3), actual open restriction
(blueprint: def-sfb-kummer-chart-geometry-maps).
Proof: both maps are the second projection of the punctured pullback square;
unfold toPuncturedBase and toOpen, and use the pullback lift projection equation. -/
theorem kummerChartToOpen_commutes (p : ℕ) (D : Y.IdealSheafData)
    (c : TameRootExtensionChart C I) :
    c.toPuncturedBase p D ≫ kummerChartToOpen D c = c.toOpen p D := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
