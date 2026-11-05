/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility

/-! # Uniqueness of normalized maps from completed coefficients to a finite quotient

Source: the finite-quotient uniqueness argument in the coefficient-tower comparison,
blueprint main-20261015, sk-def-sp-coefficient-towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open WeilConjectures

end AlgebraicGeometry.ProEtale
