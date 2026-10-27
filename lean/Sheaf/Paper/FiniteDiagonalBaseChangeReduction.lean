/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.FiniteDiagonalReductionComparisons

/-! # Coefficient reduction of the diagonal base-change factor

(blueprint: lem-pur-finite-diagonal-base-change-reduction). -/

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

/-- Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Step 3;
parent node proof Step 5.
Proof: the inverse smooth base-change map is the adjunction mate of the pullback
base-change square. Apply scalar extension to its unit-and-counit formula and use
scalar pullback balancing and reduced-counit compatibility. The same triangle
identities identify the two resulting mates. Pull along the diagonal, whose
composite with the first projection is the identity, and insert the coefficient-unit
and intrinsic realization comparisons. These are exactly omegaMap and
diagonalSectionMap, so the inverse-alpha square commutes. The argument uses no
orientation and works in relative dimension zero and for identity reductions.
(blueprint: lem-pur-finite-diagonal-base-change-reduction). -/
theorem diagonalBaseChangeReduction :
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalAlpha d f aY).inv ≫
        diagonalSectionMap P m hm hmn d f aY =
      omegaMap P m hm hmn f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalAlpha d f aY).inv := by sorry

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
