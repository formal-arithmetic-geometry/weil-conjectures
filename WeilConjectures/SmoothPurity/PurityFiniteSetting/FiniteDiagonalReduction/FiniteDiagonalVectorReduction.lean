/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons

/-! # Coefficient reduction of the normal-bundle vector factor

(blueprint: lem-pur-finite-diagonal-vector-reduction). -/

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
parent node proof Step 8.
Proof: construct the coefficient-line comparison from the root-power map, its
scalar-unit adjunct, and the rank-one root generators. Ordinary tensor balancing
identifies its tensor powers. Reduction of the ordered affine integration adjunct
follows from the supported product square and exceptional transpose compatibility.
It holds for each trivialization of the normal bundle and glues, since the
integration adjunct is intrinsic. Invert that isomorphism and restrict it to the
normal zero section. The site-comparison counit equation identifies the transported
map with normalSectionMap and the tensor-power target with proTwistMap. This proves
the displayed square for the prescribed vectorFactor, including rank zero and
arbitrary ramification; quotient flatness is never used.
(blueprint: lem-pur-finite-diagonal-vector-reduction). -/
theorem diagonalVectorReduction :
    ∃ e : CoefficientLineComparison (quotient P m hm hmn)
        P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
        P.diagonalExponent_annihilates
        (P.finiteReductionSetting m hm).diagonalExponent_annihilates X,
      (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d e =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom := by sorry

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
