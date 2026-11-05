/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionNormalFormChart
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization

/-! # Torsion normal form and its consecutive-quotient obstruction

Source: the DVR elementary-divisor calculation in steps 3--5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
