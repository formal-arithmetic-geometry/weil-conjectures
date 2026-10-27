/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.AdicPurityScalarNaturalityData
public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.RationalScalarComparisonData

/-! # The actual field purity components and coefficient-passage equations

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

/-- The trace of this very purity component under the specified exceptional adjunction.
Source: clause (6), t = epsilon P(gamma)
(blueprint: lem-sf-normalized-field-purity-trace). -/
def trace {A B : Type w} [Category.{v} A] [Category.{v} B]
    {H G : A ⥤ B} {P : B ⥤ A} (adj : P ⊣ G)
    (gamma : ∀ K : A, H.obj K ≅ G.obj K) (K : A) : P.obj (H.obj K) ⟶ K :=
  P.map (gamma K).hom ≫ adj.counit.app K

/-- The purity, inverse-purity and trace equations for a specified coefficient passage.
The inverse equation is a C(eta) = eta' b; the trace uses the same gamma and counit.
Source: clause (6), the three displayed coefficient equations
(blueprint: lem-sf-normalized-field-purity-trace). -/
structure PassageEquations {A B A' B' : Type w}
    [Category.{v} A] [Category.{v} B] [Category.{v} A'] [Category.{v} B']
    {H G : A ⥤ B} {P : B ⥤ A} {H' G' : A' ⥤ B'} {P' : B' ⥤ A'}
    (adj : P ⊣ G) (adj' : P' ⊣ G') (CX : B ⥤ B') (CY : A ⥤ A')
    (gamma : ∀ K : A, H.obj K ≅ G.obj K)
    (gamma' : ∀ K : A', H'.obj K ≅ G'.obj K)
    (a : ∀ K : A, CX.obj (H.obj K) ≅ H'.obj (CY.obj K))
    (b : ∀ K : A, CX.obj (G.obj K) ≅ G'.obj (CY.obj K))
    (c : ∀ M : B, CY.obj (P.obj M) ≅ P'.obj (CX.obj M)) : Prop where
  purity (K : A) :
    CX.map (gamma K).hom ≫ (b K).hom = (a K).hom ≫ (gamma' (CY.obj K)).hom
  inverse (K : A) :
    CX.map (gamma K).inv ≫ (a K).hom = (b K).hom ≫ (gamma' (CY.obj K)).inv
  trace (K : A) :
    CY.map (NormalizedFieldPurityTrace.trace adj gamma K) =
      (c (H.obj K)).hom ≫ P'.map (a K).hom ≫
        NormalizedFieldPurityTrace.trace adj' gamma' (CY.obj K)

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

/-- The existing prime-unit theorem transported to source residue fields.
Source: finite purity conventions, ell distinct from the base characteristic
(blueprint: lem-sf-normalized-field-purity-trace). -/
@[instance_reducible] def sourcePrimeInvertible (x : X) :
    Invertible (P.coefficients.l : X.residueField x) :=
  (show IsUnit (P.coefficients.l : X.residueField x) by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x).map
        (X.residue x).hom).invertible

/-- The existing prime-unit theorem transported to target residue fields.
Source: finite purity conventions, ell distinct from the base characteristic
(blueprint: lem-sf-normalized-field-purity-trace). -/
@[instance_reducible] def targetPrimeInvertible (y : Y) :
    Invertible (P.coefficients.l : Y.residueField y) :=
  (show IsUnit (P.coefficients.l : Y.residueField y) by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k)) y).map
        (Y.residue y).hom).invertible

attribute [local instance] sourcePrimeInvertible targetPrimeInvertible

/-- The published canonical rational component at the indicated finite coefficient field.
Source: smooth-purity transport Step 1, specified normalized lattice presentation
(blueprint: lem-sf-normalized-field-purity-trace). -/
abbrev rationalGamma (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (K : RationalScalarComparisonIdentification.RCat P.field P.coefficients E Y) :=
  RationalSmoothPurityCanonical.rationalIso
    (RationalSmoothPurityCanonical.stageSetting P E) f
    (integralExceptionalCompactification P.field f) S r K

/-- The actual rational exceptional and compact-support adjunction at the small stage.
Source: smooth-purity transport Step 2, finite-field representatives
(blueprint: lem-sf-normalized-field-purity-trace). -/
abbrev smallOperation (E : AlgebraicallyClosedCoefficients.Index
    P.coefficients.l P.coefficients.Qbar) :=
  S.ring.operation (integralExceptionalCompactification P.field f)
    (.rational (ConstructibleExceptionalCoefficients.commonField
      P.coefficients.l P.coefficients.Qbar E))

/-- The actual exceptional and compact-support adjunction on the common-stage category.
Source: smooth-purity transport Step 2, descended exceptional counit
(blueprint: lem-sf-normalized-field-purity-trace). -/
abbrev closedOperation :=
  S.ring.operation (integralExceptionalCompactification P.field f) .closed

/-- The canonical purity component in the small model, retaining its algebra equivalence.
Source: smooth-purity transport Step 2, finite-field representatives
(blueprint: lem-sf-normalized-field-purity-trace). -/
abbrev smallGamma (E : AlgebraicallyClosedCoefficients.Index
    P.coefficients.l P.coefficients.Qbar)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u}
        P.coefficients.l P.coefficients.Qbar E) Y) :=
  RationalSmoothPurityCanonical.smallModelIso
    (RationalSmoothPurityCanonical.stageSetting P E) f
    (integralExceptionalCompactification P.field f) S r K

/-- The canonical common-stage component, constructed on its literal finite presentation.
Source: smooth-purity transport Step 2
(blueprint: lem-sf-normalized-field-purity-trace). -/
abbrev closedGamma
    (K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Y) :=
  RationalSmoothPurityCanonical.commonIso P f
    (integralExceptionalCompactification P.field f) S r K

/-- The prescribed source comparison from a small finite stage into common coefficients.
It is the inverse of the published source presentation comparison on the literal pair.
Source: smooth-purity transport Step 2
(blueprint: lem-sf-normalized-field-purity-trace). -/
def commonSourceComparison (E : AlgebraicallyClosedCoefficients.Index
    P.coefficients.l P.coefficients.Qbar)
    (K : sfRationalConstructibleCategory P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u}
        P.coefficients.l P.coefficients.Qbar E) Y) :=
  (RationalSmoothPurityCanonical.commonSourceComparison
    P.coefficients.l P.coefficients.Qbar f r
      ((ConstructibleExceptionalCoefficients.commonInclusion
        P.coefficients.l P.coefficients.Qbar Y E).obj K)).symm

attribute [local irreducible] RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.commonSource sfRationalScalarExtension
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalIso RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso RationalSmoothPurityCanonical.commonSourceComparison
  commonSourceComparison


end WeilConjectures.NormalizedFieldPurityTrace
