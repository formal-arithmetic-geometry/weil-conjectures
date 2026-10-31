/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOrientationCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.NormalizedSmoothOrientationUnits

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-specified-integral-unit-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans
attribute [local irreducible]
  RationalSmoothPurityCanonical.integralIso
  RationalSmoothPurityCanonical.integralSource
  RationalSmoothPurityCanonical.representative
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.orientation
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.commonSourceComparison

section SpecifiedIntegralFamily
variable (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k)) [aX.IsOver (Spec (.of P.field.k))]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (d : ℕ) [SmoothOfRelativeDimension d aX]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := aX))
    (I : AdicPurityScalarNaturality.Data P.field P.coefficients aX d T)

/-- Normalization of the fixed simultaneous family's unit component against the
recorded trace-normalized orientation on the actual Tate line. This equation ties
its rational and common-stage realizations to that very specified integral gamma.
Source: reconstruction at the unit and uniqueness of normalized rank-one trace
(blueprint: def-pod-specified-integral-unit-orientation). -/
@[irreducible] def specifiedIntegralUnitPurityNormalization
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (core : CompletedUnitPullback.Core P.coefficients.l E.val aX) : Prop :=
  let PE := RationalSmoothPurityCanonical.stageSetting P E
  let U := smoothOrientationIntegralUnit P E
  let j := smoothIntegralUnitSourceIso P aX d E core
  let γ := RationalSmoothPurityCanonical.orientation PE aX
    (integralExceptionalCompactification P.field aX) T d
  ObjectProperty.homMk j.inv ≫ (I.gamma E).hom.app U = γ.hom ∧
    (I.gamma E).inv.app U ≫ ObjectProperty.homMk j.hom = γ.inv

end SpecifiedIntegralFamily

end WeilConjectures
