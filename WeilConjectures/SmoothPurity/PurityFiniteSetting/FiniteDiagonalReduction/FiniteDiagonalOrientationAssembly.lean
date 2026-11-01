/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationAssemblyLocal
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationAssemblyGlue

/-! # Global assembly of the specified diagonal orientation

(blueprint: lem-route-diagonal-orientation-assembly). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The chartwise diagonal assembly is the actual orientation globally.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 3--4;
parent node proof Step 9, and lem-pur-diagonal-dnc-chart-normalization.
Proof: cover Y by affine opens and X above each by affine opens admitting smooth
etale coordinates. The diagonal orientation is compatible with open base change,
by its ordinary counit normalization. The inverse base-change factor, normalized
DNC factor and zero-section restriction of the vector integration factor have
those same restriction comparisons, by exceptional base change, DNC uniqueness,
and integration locality. On each affine chart their composite equals the specified
orientation by diagonal_dnc_chart_normalization. Both composites are isomorphisms to the same
shifted Tate line. After using one
isomorphism to identify their sources, their ratio is a degree-zero endomorphism
of that line. Untwisting and cancelling its shift identifies this with an ordinary
coefficient-sheaf endomorphism, for which open restrictions detect equality.
Thus the chart equalities glue; no locality claim about arbitrary derived Ext
classes is needed. The comparisons use the prescribed
projective-line trace transport, including its empty tensor at d=0.
(blueprint: lem-route-diagonal-orientation-assembly). -/
theorem diagonalOrientationAssembly :
    (P.diagonalDualizingObject d f aY).hom =
      (P.chartDiagonalAlpha d f aY).inv ≫ (P.chartDiagonalDelta d f aY).hom ≫
        (vectorFactor P d f aY).hom := by
  obtain ⟨I, U, hU, hlocal⟩ := diagonalOrientationAssembly_affineLocal P d f aY
  exact diagonalOrientationAssembly_of_affineLocal P d f aY U hU hlocal

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
