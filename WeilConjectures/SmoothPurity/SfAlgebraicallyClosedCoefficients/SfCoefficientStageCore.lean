/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import WeilConjectures.SmoothPurity.Sf.SfRationalScalarExactOfIntegral
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Scalar.ScalarShiftNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.Rational.RationalAssociatorShiftCompat

/-! Intrinsic finite coefficient stages and their scalar coherence.
This file contains the finite-stage part of SfAlgebraicallyClosedCoefficients,
separated so its compilation is independent of the pair-category construction
(blueprint: lem-pur-intrinsic-coefficient-stage-shift-coherence).
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
namespace WeilConjectures
namespace SfAlgebraicallyClosedCoefficients

section
attribute [local irreducible] sfRationalTriangulationDatum sfRationalScalarExtension

open TensorProduct

end

section ScalarShiftCoherence

attribute [local irreducible] ScalarLocalization.composition
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar
  sfIntegralOrdinaryComparison sfIntegralScalarComp sfRationalScalarComp
  sfRationalTriangulationDatum sfRationalScalarExtension

open TensorProduct

section Integral

variable (p l : ℕ) [Fact l.Prime] (hl : l ≠ p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

attribute [local instance] normalizedIntegralShift

attribute [local irreducible] normalizedComparison

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

end Integral

end ScalarShiftCoherence

attribute [local irreducible] correctedAssociator

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum
  sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  sfIntegralScalarComp sfIntegralScalarUnit sfIntegralOrdinaryComparison
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

section

end

attribute [local irreducible] transition associator unitor
  stagePreadditive stageShift stagePretriangulated

section

attribute [local irreducible] stageCategory

-- Compare whole natural transformations before taking components. This keeps the
-- proof-irrelevant inclusion witnesses out of large functor-object conversions.

end

end SfAlgebraicallyClosedCoefficients
end WeilConjectures
