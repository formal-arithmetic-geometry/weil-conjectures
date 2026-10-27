/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.StrictDirectImageMixedUnitData

/-! # Scalar-linear reconstruction mate square

Source: Stacks Tag 0B56, equation-projection-formula-map.
(blueprint: lem-weil-strict-mixed-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictDirectImageMixedUnit
open SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Coefficient-adjunction form of the reconstruction-transported scalar square.
Source: Stacks 0B56, equation-projection-formula-map; Steps 4--5 of the strict
mixed-unit calculation (blueprint: lem-weil-strict-mixed-scalar-square).

Proof: let q be the scalar-adjunction transpose of direct image of the source scalar
unit followed by the inverse restriction comparison. The iterated-square-mates theorem
identifies q with the geometric counit/tensor mate. The normalized direct-image
compositors are conjugate to the pullback comparisons by the ringed comparison tensor
adjunction theorem. Paste the coefficient/reduction squares in both orders. On the
left-adjoint side both composites send (x tensor s) tensor b to x tensor (s-bar times b),
including every quotient transition. Successive derived quotient normalization identifies
these composites, and mate pasting gives the corresponding equality of right mates on
entire system categories. Substitute HasIntegralLaws for the integral comparison.
Reconstruction transposition gives r R(psi) = alpha; scalar reduction transposition gives
s R(chi) = e. Naturality cancels the adjacent reconstruction and completion isomorphisms.
The resulting equation is precisely the displayed scalar-adjunction square. This step
uses neither the mixed unit nor faithfulness of system evaluation. -/
theorem strictMixedScalarSquare
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (D : IntegralComparisons l Ω f) (hD : HasIntegralLaws l Ω f D)
    (e j : AlgebraicallyClosedCoefficients.Index l Ω) (h : e ≤ j)
    (EX : CoefficientDerivedSystemCalculus l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      X)
    (EY : CoefficientDerivedSystemCalculus l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      Y)
    (LX : CoefficientDerivedSystemCalculus l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      X)
    (LY : CoefficientDerivedSystemCalculus l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      Y)
    (AX : CoefficientExtensionSystems l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) X)
    (AY : CoefficientExtensionSystems l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) Y)
    (dX : CoefficientExtensionReductionData l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      e) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) X EX LX AX)
    (dY : CoefficientExtensionReductionData l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      e) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) Y EY LY AY)
    (CE : LimitComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e) f) (CL :
      LimitComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) f)
    (C : RestrictionComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) f)
    (K : sfIntegralConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      X) :
    (coefficientExtensionReductionIso l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) Y EY LY AY dY).inv.app
        ((D.integral e).image.obj K).obj ≫
      LY.reduction.map (((D.integralComparison e j h).inv.app K).hom) ≫
      reductionMap l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) f LX LY CL (D.integral
      j)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (AlgebraicallyClosedCoefficients.Coefficient.{u}
      l Ω e) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) X).obj K) ≫
      (FrobeniusExchange.systemDirect l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      f).map
        ((coefficientExtensionReductionIso l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω e j h) X EX LX AX dX).hom.app K.obj)
      =
    AY.scalar.T.map (reductionMap l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e) f EX EY
      CE (D.integral e) K) ≫
      (AY.scalar.adjunction.homEquiv _ _).symm
        ((FrobeniusExchange.systemDirect l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω e)
      f).map
            (AX.scalar.adjunction.unit.app (EX.reduction.obj K.obj)) ≫
          C.derived.inv.app (AX.scalar.T.obj (EX.reduction.obj K.obj))) := by sorry

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.StrictDirectImageMixedUnit
