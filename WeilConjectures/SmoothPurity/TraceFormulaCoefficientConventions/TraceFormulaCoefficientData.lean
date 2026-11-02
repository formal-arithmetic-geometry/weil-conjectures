/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Shared finite-field and finite-quotient trace-formula data

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/
def-trf-coefficient-conventions.md (blueprint: def-trf-coefficient-conventions).
The data is shared by the current condensed conventions and published finite interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [instance] TraceFormulaCoefficientConventions.finite_type
  TraceFormulaCoefficientConventions.quasi_compact
  TraceFormulaCoefficientConventions.separated

namespace TraceFormulaCoefficientConventions

/-- The recorded small model of the chosen finite field inside the algebraic closure.
It is transported by `Shrink.algEquiv`, retaining the field and its inclusion.
Source: blueprint (blueprint: def-trf-coefficient-conventions). -/
noncomputable abbrev coefficientField (T : TraceFormulaCoefficientConventions.{u}) : Type u :=
  Shrink.{u} T.extension.val

/-- Finite dimensionality is transported by the canonical small-model algebra equivalence.
Source: blueprint def-trf-coefficient-conventions, the chosen finite extension E.
(blueprint: def-trf-coefficient-conventions). -/
noncomputable instance coefficientFieldFinite (T : TraceFormulaCoefficientConventions.{u}) :
    FiniteDimensional (Padic T.coefficients.l) T.coefficientField :=
  Module.Finite.equiv (Shrink.algEquiv (Padic T.coefficients.l) T.extension.val).symm.toLinearEquiv

end TraceFormulaCoefficientConventions
end WeilConjectures
