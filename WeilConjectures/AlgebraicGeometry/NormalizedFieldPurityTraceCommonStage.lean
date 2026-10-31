/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedFieldPurityTraceData

/-! # Common-stage enlargement of the field purity source

Source: current blueprint, prop-functor-package.proof.md clause (6),
and smooth-purity transport Steps 1--2
(blueprint: lem-sf-normalized-field-purity-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 128

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NormalizedFieldPurityTrace

variable (P : PurityFiniteSetting.{u})
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (r : ℕ) [SmoothOfRelativeDimension r f]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

attribute [local instance] sourcePrimeInvertible targetPrimeInvertible

attribute [local irreducible] RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.commonSource sfRationalScalarExtension
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalIso RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso RationalSmoothPurityCanonical.commonSourceComparison
  commonSourceComparison

/-- The finite-extension source comparison included in the common coefficient category.
The explicit category transport is the one used by the canonical common purity map.
Source: clause (6), common-stage coefficient passage
(blueprint: lem-sf-normalized-field-purity-trace). -/
def commonSourceScalar
    (E F : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (h : E ≤ F)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u}
        P.coefficients.l P.coefficients.Qbar E) Y) :=
  let e := RationalSmoothPurityCanonical.sourceScalar P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u}
      P.coefficients.l P.coefficients.Qbar E)
    (AlgebraicallyClosedCoefficients.Coefficient.{u}
      P.coefficients.l P.coefficients.Qbar F)
    (AlgebraicallyClosedCoefficients.coefficientInclusion
      P.coefficients.l P.coefficients.Qbar E F h) f r K
  let e' := RationalSmoothPurityCanonical.transportIsoCategory _ _
    (RationalSmoothPurityCanonical.commonCategory_eq P X F) e
  (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) F).mapIso e'

attribute [local irreducible] commonSourceScalar

/-- The source comparison commutes with every enlargement of a common finite field.
Source: clause (6), common-stage coefficient cocycle
(blueprint: lem-sf-normalized-field-purity-trace). -/
@[irreducible] def CommonSourceComposition : Prop :=
  ∀ (E F : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
      (h : E ≤ F)
      (K : sfRationalConstructibleCategory P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u}
          P.coefficients.l P.coefficients.Qbar E) Y),
    (commonSourceScalar P f r E F h K).hom ≫
      (commonSourceComparison P f r F
        ((ConstructibleExceptionalCoefficients.rationalScalar
          P.coefficients.l P.coefficients.Qbar
          (ConstructibleExceptionalCoefficients.commonField
            P.coefficients.l P.coefficients.Qbar E)
          (ConstructibleExceptionalCoefficients.commonField
            P.coefficients.l P.coefficients.Qbar F)
          (AlgebraicallyClosedCoefficients.coefficientInclusion
            P.coefficients.l P.coefficients.Qbar E F h) Y).obj K)).hom ≫
      (RationalSmoothPurityCanonical.commonSource
        P.coefficients.l P.coefficients.Qbar f r).map
          ((ConstructibleExceptionalCoefficients.commonTransition
            P.coefficients.l P.coefficients.Qbar Y E F h).hom.app K) =
    (ConstructibleExceptionalCoefficients.commonTransition
      P.coefficients.l P.coefficients.Qbar X E F h).hom.app
        ((RationalSmoothPurityCanonical.rationalSource P.coefficients.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u}
            P.coefficients.l P.coefficients.Qbar E) f r).obj K) ≫
      (commonSourceComparison P f r E K).hom



end WeilConjectures.NormalizedFieldPurityTrace
