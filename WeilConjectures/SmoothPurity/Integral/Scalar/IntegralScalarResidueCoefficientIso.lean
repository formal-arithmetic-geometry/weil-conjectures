/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # The coefficient module of one uniformizer layer

Source: Serre, Local Fields, Chapter I, section 1, and the scalar residue-layer
argument of the blueprint. Multiplication by a uniformizer power identifies a
successive layer with the first quotient, with its actual quotient coefficient action.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The first coefficient quotient is a field because its defining ideal is maximal.
Source: Serre, Local Fields, Chapter I, section 1.
(blueprint: lem-sf-integral-scalar-residue-coefficient-iso). -/
@[reducible] noncomputable instance integralScalarResidueField :
    Field (Padic.coefficientExtensionRing l E 1) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hm : (Padic.coefficientExtensionIdeal l E 1).IsMaximal := by
    change (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1).IsMaximal
    rw [pow_one, hgen]
    exact hmax
  exact @Ideal.Quotient.field _ _ _ hm

variable (Y : AlgebraicGeometry.Scheme.{u})

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

end WeilConjectures
