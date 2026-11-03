/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Reconstruction in the actual completed coefficient presentation

Legacy copy (interface repository, batch a5/27): the earlier proved statement over the
actual completed coefficient presentation, kept for its importers after G6 restated
`Sheaf.Paper.ActualCompletedReductionReconstruction` over the pulled-back condensed coefficients.

The canonical quotient transitions are the adjuncts of the quotient units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] pbcCompletedComparison intrinsicPresentationRoundTrip
  reconstructionRestrictId

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] pbcScalarAdjunction pbcRestrictComp

section ScalarComputation
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)

end ScalarComputation

/-- An intrinsically complete object is a Roos limit of its actual quotient reductions.
Source: blueprint order 1270, Koszul reconstruction; Stacks Tags 091N and 0DVC.
(blueprint: lem-weil-pbc-actual-completed-reduction-reconstruction).

Proof: choose a K-flat representative in the constant completed-ring presentation
used to define intrinsic completeness. The completed Koszul reduction Roos triangle
identifies its intrinsic completion with the derived limit of its strict quotient
tower. The completeness hypothesis makes the completion map invertible, so transport
that triangle's first vertex to the given object. Transport the coefficient ring
along pbcCompletedComparison. This exact equivalence preserves countable products,
so it preserves the Roos triangle. At each finite level the normalized constant
quotient comparison identifies the transported tower with the actual quotient
extension followed by scalar restriction. The tensor-unit normalization makes the
adjacent square commute: both adjuncts are the direct quotient unit. The product of
these level isomorphisms conjugates the transition endomorphisms. Transporting the
two product vertices therefore gives the displayed distinguished Roos triangle.
No bound, constructibility, flatness, or choice of a limit functor is needed. -/
theorem pbc_actual_completed_reduction_reconstruction_legacy
    [HasCountableProducts (PbcCompletedDerived T d)]
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    let M : ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
    Functor.ofOpSequence
        (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
          ((pbcCompletedReduction T d n).obj K))
        (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
          (pbcReductionTransition (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
              ((pbcCompletedReduction T d n).obj K))
    IsDerivedLimit
      (K := fun n ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op) K := by
  dsimp only
  simp only [Functor.ofOpSequence_obj, Functor.ofOpSequence_map_homOfLE_succ]
  obtain ⟨s, b, hb, C, eC, hC⟩ := hK
  have : HasCountableProducts
      (reductionDerivedCategory T (completedReductionCoefficient T d)) :=
    inferInstanceAs (HasCountableProducts (PbcCompletedDerived T d))
  apply reconstructionLimit_transport _ _ K
    (reconstructionStrictLimit T d K s b hb C eC hC)
    (fun n ↦ (asIso (completedReductionEvaluation T d n)).app K)
  intro n
  simpa only [reconstructionStrictStep, reconstructionStep, completedTowerDerivedStep,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.app_hom, asIso_hom, Category.assoc] using
      congr_app (reconstructionStep_comparison T d n) K

end AlgebraicGeometry.Scheme
