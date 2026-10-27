/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels

/-! # Data of the normalized scalar Roos lift -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

abbrev scalarModelRoosZeroLiftType
    (_SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ) : Type _ :=
  (completedOrdinaryScalarComplex l L F j X).obj
      ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ⟶
    integralOperationsRoos
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor

def scalarModelRoosZeroLiftZero
    (SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D) : Prop :=
  ∀ i : ℤ, h.f i ≫
    (CochainComplex.mappingCocone.snd (scalarRoosBoundary
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)).v i (i - 1) (by omega) = 0

def scalarModelRoosZeroLiftCoordinates
    (SL : CoefficientDerivedSystemCalculus l L X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : (P.obj.X i).val.obj U) (y : (D.X i).val.obj (op (n, U.unop))),
    ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex
        (.up ℤ)).obj D).asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U)
      (completedScalarTensorSection l E L ι X (P.obj.X i) U t x) =
        integralComparisonRestrictedSection l L X (D.X i) n U y →
    ((h.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
      (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
          (.up ℤ)).obj D)).asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
      (completedScalarTensorSection l L F j X
        (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
        (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) =
      integralComparisonRestrictedSection l F X
        ((integralComparisonSequenceScalarModel l L F j X).E.obj (D.X i)) n U
        (integralComparisonSequenceTensorSection l L F j X (D.X i)
          (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l F X n).hom.app U s) y)

/-- The realization/transpose construction supplies a lift with its two strict
conditions. The factorization identity is deliberately isolated in the next
stage, so this theorem records only the construction data.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-core)

Proof in words: choose the simultaneous strict quotient presentation and the
K-injective tower resolution, then transpose the compatible quotient family.
The normalized realization gives the displayed coordinate formula and the
Roos differential gives the zero shifted coordinate. -/
theorem scalarModelRoosZeroLift_core
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (hf : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex
          (.up ℤ)).obj D).asFunctor)).v i (i - 1) (by omega) = 0) :
    ∃ h : scalarModelRoosZeroLiftType l E L F ι j X SL P D,
      scalarModelRoosZeroLiftZero l E L F ι j X SL P D h ∧
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h := by
  sorry

end WeilConjectures
