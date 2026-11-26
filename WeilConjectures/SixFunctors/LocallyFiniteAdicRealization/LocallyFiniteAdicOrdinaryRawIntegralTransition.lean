/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedRawIntegralFormula

/-! # Integral normalization of the ordinary finite closure comparison

Raw scalar change commutes with continuous integral realization.

## Implementation details

The inverse closure comparison is expanded into the ordinary coefficient compositor and the
scalar comparison. The raw scalar lift equation, naturality of
`continuousIntegralComparison` and the continuous integral normalization reduce the claim, after
cancelling the common invertible integral scalar comparison, to the inverse
`coefficientExtensionSquare` for the completed square of the scalar data.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.8.2 and
  Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

attribute [local irreducible] finiteCondensedClosureFunctor finiteFunctor
  pbcDerivedRestrict CoefficientPresentation.integralMap sections
  reductionDerivedChange integralDetailedTransport sfRationalConstructibleLocalization
  AlgebraicGeometry.Scheme.rationalCoefficientSheaf
  AlgebraicGeometry.Scheme.integralCoefficientSheaf pbcIntegralDatum
  completedIntegralCommRingSheafUnrestricted sfIntegralConstructible purCoefficientIso
set_option cleanup.letToHave false

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Integral realization before flattening either coefficient extension. -/
@[irreducible] def finiteOrdinaryRawIntegralModel (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteFunctor l X A.toCore E ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E) ⋙
          pbcDerivedExtend ((A.realization E).integralIso.hom ≫
            (A.realization E).inclusion) ⋙ pbcDerivedExtend (A.closure.leg E) := by
  let r := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let b := Functor.isoWhiskerRight (eqToIso (finiteRawIntegralFormula l X A E))
    (pbcDerivedExtend (A.closure.leg E))
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A.stage E).integral.functor
      (continuousIntegralComparison l X A E)) (pbcDerivedExtend (A.closure.leg E))
  let g := Functor.isoWhiskerRight (eqToIso (A.stage E).integral_identity)
    (pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E))
  exact b ≪≫ d ≪≫ g

/-- The explicit ordinary arrow retaining the raw completed integral comparison. -/
@[irreducible] def finiteOrdinaryRawIntegralTransition (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :=
  let rE := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let rL := (A.realization L).integralIso.hom ≫ (A.realization L).inclusion
  let c := (A.scalar.coefficient h).coefficient
  let j := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction c)
    (pbcDerivedScalarAdjunction (A.closure.leg L))
    (pbcDerivedScalarAdjunction (A.closure.leg E))
    (pbcDerivedRestrictComp c (A.closure.leg L) (A.closure.leg E) (A.closure.cocone h))
  let n := coefficientExtensionSquare X (pbcCompletedScalarMap l (PadicAlgCl l) X h)
    rL rE c (A.scalar.completed_square h)
  j.inv.app ((pbcDerivedExtend rE).obj
      ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj)) ≫
    (pbcDerivedExtend (A.closure.leg L)).map
      (n.inv.app
          ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj) ≫
        (pbcDerivedExtend rL).map ((A.raw.integral.comparison h).hom.app K))

attribute [local semireducible] sfRationalConstructibleLocalization

/-- Raw scalar change commutes with continuous integral realization. -/
theorem finiteOrdinaryRawIntegralModel_transition
    (A : FiniteCondensedData l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    let B :=
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
    integralTensorSquare
      ((closureComparison l X A.toCore A.scalar A.closure h).inv.app
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))
      ((finiteOrdinaryRawIntegralModel l X A E).app K)
      ((finiteOrdinaryRawIntegralModel l X A L).app B)
      (finiteOrdinaryRawIntegralTransition l X A h K) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
