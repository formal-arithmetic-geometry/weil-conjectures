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

/-- The canonical small presentation, in the scheme universe.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
def field : Type u :=
  letI : Small.{0} E := Module.Finite.small (R := Padic l) (M := E)
  letI : Small.{u} E := small_map (equivShrink.{0} E)
  Shrink.{u} E

/-- The valuation ring of the small presentation.
Source: blueprint, finite coefficient presentation
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integers := Padic.coefficientExtensionIntegers l (field.{u} l E)

/-- The continuous condensed valuation ring, with sections C(S, O).
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev integerRing :=
  DerivedNakayama.integerRing l (field.{u} l E)

/-- The internal finite quotient ring.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev quotientRing (n : ℕ) :=
  DerivedNakayama.quotientRing l (field.{u} l E) n

/-- Inverse image from the point on internal modules.
Source: blueprint, continuous coefficients and inverse image
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev pullback (X : Scheme.{u}) :=
  DerivedNakayama.pullback l (field.{u} l E) X

/-- Exact derived restriction from positive level n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev restrict (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.restrict l (Coefficients.field.{u} l E) X n

/-- The termwise product of the strict reduction tower.
Source: blueprint, canonical reduction and Roos construction
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev product (X : Scheme.{u}) (P : CochainComplex (Modules.{u} l E X) ℤ) :=
  AdicCompletion.product l (Coefficients.field.{u} l E) X P

/-- Canonical derived extension to positive level n+1.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev derivedReduction (X : Scheme.{u}) (n : ℕ) :=
  AdicCompletion.derivedReduction l (Coefficients.field.{u} l E) X n

/-- Internal modules over the pulled-back integral ring.
Source: blueprint, canonical reduction and normalized towers
(blueprint: def-sfb-small-coefficient-derived-completion). -/
abbrev Modules (X : Scheme.{u}) :=
  AdicCompletion.Modules l (Coefficients.field.{u} l E) X

end Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SmallAdicCompletion
