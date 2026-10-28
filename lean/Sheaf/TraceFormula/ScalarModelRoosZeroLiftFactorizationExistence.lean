/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore
import Sheaf.TraceFormula.ScalarModelRoosZeroLiftStrictExistence
import Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorizationFromCoordinates

/-! # Existence of a factorized normalized scalar Roos lift -/

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

/-- The realization/transpose construction has a canonical lift whose coordinates
are normalized and whose localization is the displayed scalar-realization map.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-factorization-existence)

Proof in words: choose the simultaneous strict quotient presentation used by the
scalar realization normalization, transpose the compatible quotient family, and
apply the universal cochain counit.  The resulting strict map has zero shifted
Roos coordinate, its unshifted coordinates are the quotient coordinates of `f`,
and the normalization equation identifies its localization with the displayed
scalar-realization composite.  Tensor balancing and sheafification extend the
pure-generator calculation to all sections.
-/
theorem scalarModelRoosZeroLift_factorization_exists
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (b : IntegralComparisonScalarModel l L F j X SL ρF)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor) :
    ∃ h : scalarModelRoosZeroLiftType l E L F ι j X SL P D,
      scalarModelRoosZeroLiftZero l E L F ι j X SL P D h ∧
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h ∧
      ((completedDerivedScalarExtension l L F j X).map
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
        ((completedOrdinaryScalarComplex l E L ι X).obj P.obj) ≫ DerivedCategory.Q.map h) := by
  obtain ⟨h, hh, hcoord⟩ := scalarModelRoosZeroLift_strict_exists
    l E L F ι j X SL ρL ρF b P D f
  refine ⟨h, hh, hcoord, ?_⟩
  exact scalarModelRoosZeroLift_factorization_from_coordinates
    l E L F ι j X SL ρL ρF b P D f h hh hcoord

end WeilConjectures
