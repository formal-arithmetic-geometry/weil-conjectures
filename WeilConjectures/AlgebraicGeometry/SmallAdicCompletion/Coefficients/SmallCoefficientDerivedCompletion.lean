/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Derived completion on the canonical small coefficient presentation

Source: blueprint, sec-proetale-coefficients,
`sk-def-pe-derived-completion/_section.md`, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion).

Finite dimensionality makes E small in every scheme universe. The existing continuous
coefficient and Roos constructions are applied to its canonical Shrink presentation.
No second tensor product, quotient tower, or completion construction is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.SmallAdicCompletion

namespace Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Inverse image from the point on internal modules.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev pullback (X : Scheme.{u}) :=
  DerivedNakayama.pullback l (field.{u} l E) X

end Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SmallAdicCompletion
