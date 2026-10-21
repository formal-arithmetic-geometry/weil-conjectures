/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted

/-! # Reconstruction in the actual completed coefficient presentation

The canonical quotient transitions are the adjuncts of the quotient units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

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
theorem pbc_actual_completed_reduction_reconstruction
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
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op) K := by sorry

end AlgebraicGeometry.Scheme
