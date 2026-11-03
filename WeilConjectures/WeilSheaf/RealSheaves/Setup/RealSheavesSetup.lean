/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Complex.Basic
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.PointCount
public import WeilConjectures.AlgebraicGeometry.Curve

import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fields, curves and Frobenius for real sheaves

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-setup,
Definition d-real-setup, order 2920 (blueprint: d-real-setup).

The field choices, curve predicate, closed-point notation and affine-open predicate
use the existing field, scheme, pure-dimension, base-change and Frobenius definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RealSheaves

set_option linter.checkUnivs false in
attribute [instance] Setup.baseField Setup.baseFintype Setup.closureField
  Setup.closureAlgebra Setup.closure Setup.l_prime Setup.coefficientField
  Setup.coefficientAlgebra Setup.coefficientClosure

/-- The fixed cardinality `q = p^a`.
Source: blueprint main-20261015, d-real-setup, first paragraph (blueprint: d-real-setup). -/
abbrev Setup.q (D : Setup.{u, v}) : ℕ := D.p ^ D.a

/-- Scalar extension to the chosen algebraic closure, using the recorded fibre product.
Source: blueprint main-20261015, d-real-setup, curve paragraph (blueprint: d-real-setup). -/
abbrev Setup.geometricCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] : Scheme.{u} :=
  pullback (C₀ ↘ Spec (.of D.k₀))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Precisely the chapter's curve convention: nonempty, separated, smooth and finite type,
of pure dimension one, and connected after extension to the chosen algebraic closure.
Source: blueprint main-20261015, d-real-setup, curve paragraph (blueprint: d-real-setup). -/
def Setup.IsCurve (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] : Prop :=
  Nonempty C₀ ∧ IsSeparated (C₀ ↘ Spec (.of D.k₀)) ∧
    Smooth (C₀ ↘ Spec (.of D.k₀)) ∧ LocallyOfFiniteType (C₀ ↘ Spec (.of D.k₀)) ∧
    QuasiCompact (C₀ ↘ Spec (.of D.k₀)) ∧ C₀.IsPureDimension 1 ∧
    ConnectedSpace (D.geometricCurve C₀)

/-- Geometric Frobenius on the chosen algebraic closure, reusing the inverse of arithmetic
Frobenius, which raises elements to `#k₀ = q`.
Source: blueprint main-20261015, d-real-setup, Frobenius paragraph (blueprint: d-real-setup). -/
abbrev Setup.frobenius (D : Setup.{u, v}) : D.k ≃ₐ[D.k₀] D.k :=
  FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k

end RealSheaves
