/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore
import Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationExistence
import Sheaf.TraceFormula.ScalarModelRoosZeroLiftUniqueness

/-! # Factorization of the normalized scalar Roos lift -/

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

def scalarModelRoosZeroLiftFactorization
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D) : Prop :=
  (completedDerivedScalarExtension l L F j X).map
      (DerivedCategory.Q.map f ≫ (integralComparisonRoosBridge l L X ρL D).inv) ≫
    (completedScalarComparison l L F j X).app
      ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
    b.realization.hom.app
      ((coefficientSequenceLimit l L X).obj (DerivedCategory.Q.obj D)) ≫
    (coefficientSequenceLimit l F X).map
      ((integralComparisonDerivedSequenceScalar l L F j X).map
        (SL.adjunction.counit.app (DerivedCategory.Q.obj D))) ≫
    (coefficientSequenceLimit l F X).map
      ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
    (integralComparisonRoosBridge l F X ρF _).hom =
  completedScalarCounit l L F j X
    ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h

/-- The normalized lift factors through the completed scalar counit once its
zero-shift and quotient-coordinate identities are fixed.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-factorization)

Proof in words: apply the universal cochain counit to the normalized quotient
coordinates. Naturality of the realization and Roos bridge identifies the two
sides on tensor generators; the zero-shift equation removes the signed term,
and the quotient universal property extends the equality to all sections. -/
theorem scalarModelRoosZeroLift_factorization
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor)
    (h : scalarModelRoosZeroLiftType l E L F ι j X SL P D)
    (hh : scalarModelRoosZeroLiftZero l E L F ι j X SL P D h)
    (hcoord : scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h) :
    scalarModelRoosZeroLiftFactorization l E L F ι j X SL ρL ρF b P D f h := by
  obtain ⟨g, hg, hcoordg, hfactor⟩ :=
    scalarModelRoosZeroLift_factorization_exists l E L F ι j X SL ρL ρF b P D f
  have hcoord : ∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : (P.obj.X i).val.obj U),
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
      ((g.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
            (.up ℤ)).obj D)).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ)).obj
            (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
              (.up ℤ)).obj D)).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l L F j X
          (((completedOrdinaryScalarComplex l E L ι X).obj P.obj).X i) U s
          (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)) := by
    intro n i U s t x
    let z : (((coefficientSequenceRestriction l L X).obj (D.X i)).obj (op n)).val.obj U :=
      ((f.f i ≫ (CochainComplex.mappingCocone.fst (scalarRoosBoundary
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
          D).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor.obj (op m)) n).f i).val.app U)
        (completedScalarTensorSection l E L ι X (P.obj.X i) U t x)
    let y : (D.X i).val.obj (op (n, U.unop)) :=
      cast (integralComparisonRestrictedSectionType l L X (D.X i) n U) z
    have hy : integralComparisonRestrictedSection l L X (D.X i) n U y = z := by
      dsimp [y, z]
      simp only [integralComparisonRestrictedSection, cast_cast, cast_eq]
    have hy' : z = integralComparisonRestrictedSection l L X (D.X i) n U y := hy.symm
    have hh' := hcoord n i U s t x y hy'
    have hg' := hcoordg n i U s t x y hy'
    exact hh'.trans hg'.symm
  have hq := scalarModelRoosZeroLift_uniqueness l E L F ι j X P D h g hh hg hcoord
  calc
    _ = completedScalarCounit l L F j X
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map g :=
      hfactor
    _ = _ := by rw [hq]

end WeilConjectures
