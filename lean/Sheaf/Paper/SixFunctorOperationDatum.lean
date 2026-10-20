/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Paper.SixFunctorOperationDatumStages

/-!
# Six-functor operation datum

Source: blueprint master, sec-smooth-purity/sk-def-sf-operations,
def-fix-six-functor-datum (blueprint: def-fix-six-functor-datum), order 1491.

The datum is construction data, including the comparisons, rather than a choice
from an unnormalized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w v' w' hA hB hA' hB'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.SuppliedExchangeProjection
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures
open TensorProduct
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- All coefficient levels with the finite, completed, localized and common-stage
normalizations. Source: all five clauses of def-fix-six-functor-datum
(blueprint: def-fix-six-functor-datum). -/
structure SixFunctorOperationDatum
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    extends SixFunctorFiniteOperations D C E n hn where
  higher : SixFunctorHigherOperations D C E
  integralNormalization : SixFunctorIntegralNormalization D C E higher
  closure : SixFunctorCommonStages D C
  coefficientIntegralNormalization : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SixFunctorIntegralNormalization D C (Coefficient.{u} C.l C.Qbar E₀)
      (closure.coefficientStages E₀)
  commonStageCoherence : SixFunctorCommonStageCoherence closure
  /- Scalar identity and cocycle equations are theorems of the coefficient
     comparison modules; the datum records the comparison isomorphisms above. -/

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.finiteVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.finiteDuality.verdier (sixFunctorFiniteHom D C E n hn) X c

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.integralVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.higher.integralDuality.verdier (fun X ↦ constructibleIntegralHom C.l E X.obj.left) X c

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.rationalVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.higher.rationalDuality.verdier (fun X ↦ rationalDerivedInternalHom C.l E X.obj.left) X c

/-- Verdier dual at this coefficient level is the recorded derived internal Hom
into the exceptional image of its coefficient unit, including the morphism action.
Source: clause (5) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.commonStageVerdier
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  S.closure.commonStageDuality.verdier
    (fun X ↦ commonStageDerivedInternalHom C.l C.Qbar X.obj.left) X c

/-- The finite tensor on the finite-Tor category. It is the recorded derived tensor,
not another bifunctor chosen as data.
Source: clause (1) (blueprint: def-fix-six-functor-datum). -/
abbrev SixFunctorOperationDatum.finiteTensor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) := S.finiteTensorDomainStage X

/-- Finite internal Hom on its exact bounded-output pair domain.
Source: clause (1) (blueprint: def-fix-six-functor-datum). -/
abbrev SixFunctorOperationDatum.finiteInternalHom
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) := sixFunctorFiniteHom D C E n hn X

/-- The finite-Tor domain is the recorded predicate, restricted to the bounded
constructible category. Source: the initial domains
(blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.finiteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) : ObjectProperty (sixFunctorFiniteCategory D C E n hn X) :=
  fun K ↦ finiteTorConstructible C.l E n hn X.obj.left K.obj

/-- The integral finite-Tor domain is the recorded uniform finite-reduction condition.
Source: the initial domains (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.integralFiniteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) : ObjectProperty (sfIntegralConstructibleCategory C.l E X.obj.left) :=
  fun K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj

/-- At field coefficients finite Tor is the entire recorded constructible category.
Source: the initial domains (blueprint: def-fix-six-functor-datum). -/
abbrev SixFunctorOperationDatum.rationalFiniteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) :=
  finiteTorFieldCoefficientCategory (sfRationalConstructibleCategory C.l E X.obj.left)

/-- The common-stage finite-Tor category uses the same field-coefficient convention.
Source: the initial domains (blueprint: def-fix-six-functor-datum). -/
abbrev SixFunctorOperationDatum.commonStageFiniteTorDomain
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (X : SixFunctorSpace D) :=
  finiteTorFieldCoefficientCategory
    (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)

/-- The finite exchange/projection triple is the dependency's mate, proper/open paste,
and projection mate. Only projection inputs are restricted to finite Tor; the
exchange inputs range over the full bounded constructible category. The inputs
and outputs use the specified intrinsic realization; every intermediate arrow is
the canonical fixed-scalar construction, with no supplied exchange-stage choices.
Source: clause (3) (blueprint: def-fix-six-functor-datum). -/
def SixFunctorOperationDatum.finiteExchangeProjection
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorOperationDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (Functor.whiskerRight
    (Functor.whiskerLeft
      ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
        (sixFunctorFiniteRealization D C E n hn Q.X).inverse)
      (AlgebraicGeometry.ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
        Q.square.toCommSq))
    (sixFunctorFiniteRealization D C E n hn Q.Y').functor,
    Functor.whiskerRight
      (Functor.whiskerLeft
        ((intrinsicFiniteTorsionConstructible C.l E n hn Q.X.obj.left).ι ⋙
          (sixFunctorFiniteRealization D C E n hn Q.X).inverse)
        (AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          Q.square Q.compactification))
      (sixFunctorFiniteRealization D C E n hn Q.Y').functor,
    Functor.whiskerRight
      (Functor.whiskerLeft
        ((finiteTorConstructible C.l E n hn Q.X.obj.left).ι ⋙
          (sixFunctorFiniteRealization D C E n hn Q.X).inverse)
        (Functor.whiskerRight
          (AlgebraicGeometry.ProEtale.projectionMapOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
            Q.compactification)
          ((Functor.whiskeringLeft _ _ _).obj
            ((finiteTorConstructible C.l E n hn Q.Y.obj.left).ι ⋙
              (sixFunctorFiniteRealization D C E n hn Q.Y).inverse))))
      ((Functor.whiskeringRight _ _ _).obj
        (sixFunctorFiniteRealization D C E n hn Q.Y).functor))

end WeilConjectures
