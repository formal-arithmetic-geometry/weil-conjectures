/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.ScalarModelRoosZeroLiftCore
import WeilConjectures.TraceFormula.ScalarModelRoosZeroLiftStrictification

/-! # Strict scalar Roos lift without a chosen coordinate presentation -/

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

/-- The strict zero-shift and quotient-coordinate part of the scalar Roos construction.

Source: Stacks 06YY, 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-strict-existence)

Proof in words: choose the simultaneous strict quotient presentation used by the
realization normalization, transpose its compatible quotient family through ordinary
scalar extension, and assemble the compatible coordinates with the mapping-cocone
universal property.  The quotient transition equations kill the Roos boundary,
which gives the zero shifted coordinate; the quotient tensor formula gives the
coordinate predicate.  The remaining normalization equation is supplied separately
by the factorization step.
-/
theorem scalarModelRoosZeroLift_strict_exists
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
      scalarModelRoosZeroLiftCoordinates l E L F ι j X SL P D f h := by
  obtain ⟨f₀, hf₀, hcoord₀⟩ := scalarModelRoosZeroLift_strictify l E L ι X P D f
  obtain ⟨h, hh, hcoord⟩ := scalarModelRoosZeroLift_core
    l E L F ι j X SL ρL ρF b P D f₀ hf₀
  refine ⟨h, hh, ?_⟩
  intro n i U s t x y hxy
  apply hcoord n i U s t x y
  rw [hcoord₀ n i U]
  exact hxy

end WeilConjectures
