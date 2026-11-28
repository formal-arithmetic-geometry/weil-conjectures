/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicOrdinaryRawIntegralTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSquareMates
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRawCompletionComparison

/-! # Integral normalization of the ordinary finite closure comparison

The completion comparison is preserved by the prescribed integral coefficient tensor transport.

## Implementation details

The coefficient model and the raw transition are written as transported tensor comparisons
through coefficient squares, and the raw ambient comparison is the transported completion map
(`FiniteCondensedData.rawComparison_hom_app`). The pasting law of these comparisons
(`integralTensorSquare_of_tensorThroughCoefficientSquare`) then gives the claim. All coefficient
maps are taken with source the completed coefficients of `Coefficient E`, so that the composite
functors are syntactically those of the pasting law.

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

/-- Integral coefficient transport after the continuous realization, with the
ordinary coefficient extensions still separate on its source. -/
@[irreducible] def finiteOrdinaryCoefficientIntegralModel (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E) ⋙
          pbcDerivedExtend ((A.realization E).integralIso.hom ≫
            (A.realization E).inclusion) ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((C.coefficient E).integralMap l X) ⋙
          pbcDerivedRestrict
            (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)) := by
  letI := C.commutative
  let I := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let r := realizationCoefficientMap l X A E
  let s := r ≫ A.closure.leg E
  let t := ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)
  letI := sectionRingMap_isIso X (condensedNativeMap l X)
  let m := tensorThroughCoefficientSquare X (purCoefficientIso l
      (Coefficient.{u} l (PadicAlgCl l) E) X) (asIso t) s
    ((C.coefficient E).integralMap l X) (finiteOrdinaryCoefficientSquare l X A C E)
  let c : pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      pbcDerivedExtend s :=
    Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction r)
      (pbcDerivedScalarAdjunction (A.closure.leg E)) (pbcDerivedScalarAdjunction s)
      (pbcDerivedRestrictComp r (A.closure.leg E) s rfl)
  let f := Functor.isoWhiskerLeft (I ⋙ integralDetailedTransport X l
    (Coefficient.{u} l (PadicAlgCl l) E)) c
  let j := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft I (eqToIso (integralDetailedTransport_eq l X
      (Coefficient.{u} l (PadicAlgCl l) E)))) (pbcDerivedExtend s)
  let k := Functor.isoWhiskerLeft I m.symm
  exact f ≪≫ j ≪≫ k

/-- `finiteOrdinaryCoefficientIntegralModel` as a transported tensor comparison through its
coefficient square. -/
theorem finiteOrdinaryCoefficientIntegralModel_eq (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    letI := sectionRingMap_isIso X (condensedNativeMap l X)
    finiteOrdinaryCoefficientIntegralModel l X A C E =
      Functor.isoWhiskerLeft
          ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
            integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E))
          (Adjunction.leftAdjointCompIso
            (pbcDerivedScalarAdjunction (realizationCoefficientMap l X A E))
            (pbcDerivedScalarAdjunction (A.closure.leg E))
            (pbcDerivedScalarAdjunction (realizationCoefficientMap l X A E ≫ A.closure.leg E))
            (pbcDerivedRestrictComp _ (A.closure.leg E) _ rfl)) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft
            (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
            (eqToIso (integralDetailedTransport_eq l X (Coefficient.{u} l (PadicAlgCl l) E))))
          (pbcDerivedExtend (realizationCoefficientMap l X A E ≫ A.closure.leg E)) ≪≫
        Functor.isoWhiskerLeft (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
          (tensorThroughCoefficientSquare X
            (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X)
            (asIso (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)))
            (realizationCoefficientMap l X A E ≫ A.closure.leg E)
            ((C.coefficient E).integralMap l X) (finiteOrdinaryCoefficientSquare l X A C E)).symm :=
  finiteOrdinaryCoefficientIntegralModel.eq_1 l X A C E

/-- `finiteOrdinaryRawIntegralTransition` through the coefficient maps of the fixed closure. -/
theorem finiteOrdinaryRawIntegralTransition_eq (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    finiteOrdinaryRawIntegralTransition l X A h K =
      (Adjunction.leftAdjointCompIso
          (pbcDerivedScalarAdjunction (A.scalar.coefficient h).coefficient)
          (pbcDerivedScalarAdjunction (A.closure.leg L))
          (pbcDerivedScalarAdjunction (A.closure.leg E))
          (pbcDerivedRestrictComp _ (A.closure.leg L) (A.closure.leg E)
            (A.closure.cocone h))).inv.app
          ((pbcDerivedExtend (realizationCoefficientMap l X A E)).obj
            ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K))) ≫
        (pbcDerivedExtend (A.closure.leg L)).map
          ((coefficientExtensionSquare X (coefficientCompletedScalarMap l X h)
              (realizationCoefficientMap l X A L) (realizationCoefficientMap l X A E)
              (A.scalar.coefficient h).coefficient
              (coefficientCompletedScalarMap_comp_realizationCoefficientMap l X A h)).inv.app
              ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj
                ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K)) ≫
            (pbcDerivedExtend (realizationCoefficientMap l X A L)).map
              ((A.raw.integral.comparison h).hom.app K)) :=
  finiteOrdinaryRawIntegralTransition.eq_1 l X A h K

/-- The completion comparison is preserved by the prescribed coefficient tensor
transport, independently of raw-stage rationalization or section reconstruction. -/
theorem finiteOrdinaryCoefficientIntegralModel_transition
    (A : FiniteCondensedData l X) (C : CoefficientSystem l X) :
    letI := C.commutative
    let R := pbcDerivedRestrict
      (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))
    ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      let T := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        E L h).obj K
      let t :=
        (pbcReductionNormalization
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h) X)
          ((C.coefficient L).integralMap l X) ((C.coefficient E).integralMap l X)
          (C.coefficient_scalar E L h) K.obj).inv ≫
        (pbcDerivedExtend ((C.coefficient L).integralMap l X)).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)).app
              K.obj)
      integralTensorSquare (finiteOrdinaryRawIntegralTransition l X A h K)
        ((finiteOrdinaryCoefficientIntegralModel l X A C E).app K)
        ((finiteOrdinaryCoefficientIntegralModel l X A C L).app T) (R.map t) := by
  intro R E L h K T t
  have := sectionRingMap_isIso X (condensedNativeMap l X)
  exact integralTensorSquare_of_tensorThroughCoefficientSquare
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X)
    (asIso (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X)))
    (realizationCoefficientMap l X A E) (realizationCoefficientMap l X A L)
    (A.scalar.coefficient h).coefficient (A.closure.leg E) (A.closure.leg L)
    (A.closure.cocone h) (coefficientCompletedScalarMap l X h)
    (coefficientCompletedScalarMap_comp_realizationCoefficientMap l X A h)
    (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h) X)
    ((C.coefficient E).integralMap l X) ((C.coefficient L).integralMap l X)
    (C.coefficient_scalar E L h) (purCoefficientIso_hom_comp_completedCoefficientMap_index l X h)
    (finiteOrdinaryCoefficientSquare l X A C E) (finiteOrdinaryCoefficientSquare l X A C L)
    (integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E))
    (integralDetailedTransport_eq l X (Coefficient.{u} l (PadicAlgCl l) E))
    (integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) L))
    (integralDetailedTransport_eq l X (Coefficient.{u} l (PadicAlgCl l) L))
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι K T
    ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h)).app
        ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K))
    ((A.raw.integral.comparison h).hom.app K) (A.rawComparison_hom_app h K)
    (finiteOrdinaryRawIntegralTransition l X A h K)
    (finiteOrdinaryRawIntegralTransition_eq l X A h K)
    (finiteOrdinaryCoefficientIntegralModel l X A C E)
    (finiteOrdinaryCoefficientIntegralModel_eq l X A C E)
    (finiteOrdinaryCoefficientIntegralModel l X A C L)
    (finiteOrdinaryCoefficientIntegralModel_eq l X A C L)

end WeilConjectures.LocallyFiniteAdicRealization
