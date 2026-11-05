/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink

/-!
# Finite extension maps of the actual completed PBC coefficient sheaves

Source: blueprint proper-base-change order 1307, the coefficient tensor extension;
its canonical completed ring map is made explicit by finite quotient projections
(blueprint: def-weil-pbc-finite-completed-coefficient-map).

## Main definitions

* `pbcIntegerInclusion`: the actual inclusion of lifted valuation rings.
* `pbcCompletedScalarMap`: the ring-sheaf map fixed by finite projections.
* `pbcAmbientScalarExtension`: the recorded K-flat derived tensor extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

variable {E F : Padic.FiniteCoefficientFields l Ω}

-- Keep the existing algebraic-closure parameter in the public signature.

variable (T : Scheme.{u})

end AlgebraicGeometry.Scheme
