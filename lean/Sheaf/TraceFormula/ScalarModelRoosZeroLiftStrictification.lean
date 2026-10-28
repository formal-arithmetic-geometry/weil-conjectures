/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore

/-! # Strictification of a scalar Roos map -/

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
  (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})

/-- Every scalar Roos map admits a strict zero-shift representative with the same
unshifted quotient coordinates.

Source: Stacks 06YY and 0941; Bhatt--Scholze, Definition 3.4.10.
(blueprint: lem-trf-scalar-model-roos-zero-lift-strictification)

Proof in words: transpose the compatible quotient family of the map through the
constant-tower/limit adjunction.  The transpose has zero shifted coordinate, and
its projections are the original unshifted Roos coordinates.  The quotient
transition equations and the chain-map equation establish compatibility in every
cochain degree; the universal property of the mapping cocone then assembles the
strict representative. -/
theorem scalarModelRoosZeroLift_strictify
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    (f : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
      (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor) :
    ∃ f₀ : (completedOrdinaryScalarComplex l E L ι X).obj P.obj ⟶ integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj D).asFunctor,
      (∀ i : ℤ, f₀.f i ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).v
          i (i - 1) (by omega) = 0) ∧
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ),
        (f₀.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U =
        (f.f i ≫ (CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ (((coefficientSequenceRestriction l L X).mapHomologicalComplex
            (.up ℤ)).obj D).asFunctor.obj (op m)) n).f i).val.app U) := by
  sorry

end WeilConjectures
