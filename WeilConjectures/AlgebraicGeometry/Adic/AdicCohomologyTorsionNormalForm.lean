/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Adic.AdicUnliftedPerfectCharts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Torsion normal form and its consecutive-quotient obstruction

Source: the DVR elementary-divisor calculation in steps 3--5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
