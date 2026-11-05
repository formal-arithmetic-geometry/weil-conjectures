/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.TensorProduct.Finite

/-! # The explicit algebraic complex for a successive coefficient layer

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: def-weil-pbc-finite-quotient-layer-tensor-complex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
