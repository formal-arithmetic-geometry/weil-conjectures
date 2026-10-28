/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.FiniteDiagonalReductionComparisons

/-! # Coefficient reduction of the normalized diagonal DNC factor

(blueprint: lem-pur-finite-diagonal-dnc-reduction). -/

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

/-- Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 3--4;
parent node proof Steps 6--7.
Proof: use centred etale coordinates near the diagonal. The support-restriction
and normal-coordinate maps are exceptional mates and hence commute with scalar
extension by pullback balancing and reduced-counit compatibility. The normal frame
maps the coefficient-independent class of y_i-x_i to d x_i. In every such chart,
conjugating the reduced DNC map by its two section coefficient comparisons has
identity standard reading: the original DNC map does, and both coordinate squares
commute. Coordinate normalization and uniqueness of DNC invariance therefore give
the DNC map at the reduced level. Etale locality glues the equality globally.
The empty coordinate frame gives the same argument when d=0.
(blueprint: lem-pur-finite-diagonal-dnc-reduction). -/
theorem diagonalDncReduction :
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalDelta d f aY).hom ≫
        normalSectionMap P m hm hmn d f aY =
      diagonalSectionMap P m hm hmn d f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalDelta d f aY).hom := by sorry

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
