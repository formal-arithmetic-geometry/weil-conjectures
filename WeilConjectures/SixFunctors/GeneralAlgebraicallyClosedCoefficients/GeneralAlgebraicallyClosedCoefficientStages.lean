/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfAlgebraicallyClosedCoefficients

import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.CategoryTheory.Whiskering

/-! # Normalized scalar stages for algebraically closed coefficients

The scalar-stage part of the intrinsic common-stage construction is isolated here
so that normalization and pair-category constructions compile independently.
Source: the scalar-stage steps of blueprint order 1462
(blueprint: lem-general-algebraically-closed-coefficient-stages).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] ScalarLocalization.category

attribute [local irreducible] sfRationalConstructibleLocalization
  sfRationalTriangulationDatum sfRationalScalarExtension
  sfRationalScalarComp sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit
  sfIntegralOrdinaryComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

end

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

end

section
attribute [local semireducible] ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition

end

attribute [local irreducible] scalarAssociator

attribute [local irreducible] associator

attribute [local irreducible] normalizedAssociator

attribute [local irreducible] transition

-- Compare whole natural transformations before taking components. This keeps the
-- proof-irrelevant inclusion witnesses out of large functor-object conversions.

attribute [local irreducible] stageCategory

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
