/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SequentialSemilinearHomCoordinates
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Normalization of the shifted coinduced Hom coordinates

Source: Stacks 0145, 015F and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

attribute [local implicit_reducible] CoinducedSequence.productFunctor
  CoinducedSequence.relationsFunctor
open Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The negative-degree product differential is exactly the stated vertex-edge difference.
Source: Stacks 0145, 015F, 0941
(blueprint: lem-sf-sequential-semilinear-hom-normalization).
Proof: transpose product projections, so the ordinary defect is the difference of
the two transition composites. Move the source shift through the actual transition,
which commutes with shifts. The restriction-shift comparison cancels on the first
composite; the second becomes exactly the prescribed shifted target transition. -/
theorem vertexCoordinatesNeg_difference
    {M N : DerivedCategory (StrictRingSystem B)} (b : M⟦(1 : ℤ)⟧ ⟶ product B N) :
    edgeCoordinatesNeg B M N (b ≫ difference B N) =
      Helper.difference B M N (-1) (vertexCoordinatesNeg B M N b) := by
  funext n
  let E := derivedSystemEvaluation B n
  let F := derivedSystemEvaluation B (n + 1)
  let S := adjacentRestriction B n
  let t := systemDerivedTransition B (Nat.le_succ n)
  let c := productHomEquiv B (M⟦(1 : ℤ)⟧) N b
  have hl : evaluationSourceShiftHomEquiv F M (S.obj (E.obj N))
      (t.app (M⟦(1 : ℤ)⟧) ≫ S.map (c n)) ≫
      (S.commShiftIso (-1)).inv.app (E.obj N) =
    t.app M ≫ S.map (evaluationSourceShiftHomEquiv E M (E.obj N) (c n)) := by
    rw [evaluationSourceShiftHomEquiv_apply, Functor.map_comp]
    have hu := evaluationShiftUnit_transformation t M
    rw [← Category.assoc, hu]
    simpa only [Category.assoc, evaluationSourceShiftHomEquiv_apply] using
      congrArg (fun z ↦ t.app M ≫ z) (evaluationShiftUnit_composite E S M (c n))
  have hr : evaluationSourceShiftHomEquiv F M (S.obj (E.obj N))
      (c (n + 1) ≫ t.app N) ≫ (S.commShiftIso (-1)).inv.app (E.obj N) =
    evaluationSourceShiftHomEquiv F M (F.obj N) (c (n + 1)) ≫
      shiftedTransition B N (-1) n := by
    simp only [evaluationSourceShiftHomEquiv_apply, Functor.map_comp,
      shiftedTransition, Category.assoc]
    rfl
  have hd := CoinducedSequence.relationsHomEquiv_defect
    (derivedSystemEvaluation B) (derivedRight B) (derivedAdjunction B)
    (adjacentRestriction B) (fun n ↦ systemDerivedTransition B (Nat.le_succ n)) b n
  change evaluationSourceShiftHomEquiv F M (S.obj (E.obj N))
    (relationsHomEquiv B (M⟦(1 : ℤ)⟧) N (b ≫ difference B N) n) ≫
      (S.commShiftIso (-1)).inv.app (E.obj N) = _
  change relationsHomEquiv B (M⟦(1 : ℤ)⟧) N (b ≫ difference B N) n = _ at hd
  rw [hd, map_sub, Preadditive.sub_comp, hl, hr]
  rfl

/-- Zero-shift transport of a transition is the original transition in zero coordinates.
Source: Stacks 0145
(blueprint: lem-sf-sequential-semilinear-hom-normalization).
Proof: use naturality of shift zero at the transition and the zero coherence axiom
of the scalar-restriction shift comparison. -/
theorem shiftedTransition_zero (N : DerivedCategory (StrictRingSystem B)) (n : ℕ) :
    (shiftFunctorZero (DerivedCategory (systemLevel B (n + 1))) ℤ).inv.app
        ((derivedSystemEvaluation B (n + 1)).obj N) ≫ shiftedTransition B N 0 n =
      (systemDerivedTransition B (Nat.le_succ n)).app N ≫
        (adjacentRestriction B n).map
          ((shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).inv.app
            ((derivedSystemEvaluation B n).obj N)) := by
  dsimp only [shiftedTransition]
  rw [Functor.commShiftIso_zero]
  simp only [Functor.CommShift.isoZero, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Category.assoc]
  rw [← Category.assoc, ← NatTrans.naturality]
  simp only [Functor.id_map, Functor.comp_obj, Helper.adjacentRestriction,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.assoc, Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]

/-- The zero-degree product differential is exactly the stated vertex-edge difference.
Source: Stacks 0145, 015F, 0941
(blueprint: lem-sf-sequential-semilinear-hom-normalization).
Proof: transpose the product projections, distribute postcomposition over subtraction,
and use the zero-shift transition identity on the target-transition term. -/
theorem vertexCoordinatesZero_difference
    {M N : DerivedCategory (StrictRingSystem B)} (b : M ⟶ product B N) :
    edgeCoordinatesZero B M N (b ≫ difference B N) =
      Helper.difference B M N 0 (vertexCoordinatesZero B M N b) := by
  funext n
  have hd := CoinducedSequence.relationsHomEquiv_defect
    (derivedSystemEvaluation B) (derivedRight B) (derivedAdjunction B)
    (adjacentRestriction B) (fun n ↦ systemDerivedTransition B (Nat.le_succ n)) b n
  change relationsHomEquiv B M N (b ≫ difference B N) n ≫
      (adjacentRestriction B n).map
        ((shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).inv.app
          ((derivedSystemEvaluation B n).obj N)) = _
  change relationsHomEquiv B M N (b ≫ difference B N) n = _ at hd
  rw [hd, Preadditive.sub_comp]
  have hz (k : ℕ) : vertexCoordinatesZero B M N b k =
      productHomEquiv B M N b k ≫
        (shiftFunctorZero (DerivedCategory (systemLevel B k)) ℤ).inv.app
          ((derivedSystemEvaluation B k).obj N) := rfl
  simp only [Helper.difference, hz, Functor.map_comp, Category.assoc,
    shiftedTransition_zero]

/-- Negative-degree edge coordinates are natural in both source and target.
Source: Stacks 0145, 015F
(blueprint: lem-sf-sequential-semilinear-hom-normalization).
Proof: transposition is natural in both variables. Shift the resulting composition,
use naturality of the source-shift unit and the scalar-restriction shift comparison,
and cancel its inverse. -/
theorem edgeCoordinatesNeg_natural
    {M M' N N' : DerivedCategory (StrictRingSystem B)}
    (f : M' ⟶ M) (g : N ⟶ N') (b : M⟦(1 : ℤ)⟧ ⟶ relations B N) :
    edgeCoordinatesNeg B M' N'
      (f⟦(1 : ℤ)⟧' ≫ b ≫ (relationsFunctor B).map g) =
        edgeMap B f g (-1) (edgeCoordinatesNeg B M N b) := by
  funext n
  let E := derivedSystemEvaluation B (n + 1)
  let S := adjacentRestriction B n
  let d := relationsHomEquiv B (M⟦(1 : ℤ)⟧) N b n
  have hd := CoinducedSequence.relationsHomEquiv_natural
    (derivedSystemEvaluation B) (derivedRight B) (derivedAdjunction B)
    (adjacentRestriction B) (f⟦(1 : ℤ)⟧') g b n
  change evaluationSourceShiftHomEquiv E M' _
    (relationsHomEquiv B (M'⟦(1 : ℤ)⟧) N'
      (f⟦(1 : ℤ)⟧' ≫ b ≫ (relationsFunctor B).map g) n) ≫
        (S.commShiftIso (-1)).inv.app ((derivedSystemEvaluation B n).obj N') = _
  rw [hd]
  simp only [evaluationSourceShiftHomEquiv_apply, Functor.map_comp, Category.assoc]
  have hu := evaluationShiftUnit_natural E f
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← hu]
  simp only [Category.assoc]
  change E.map f ≫ (evaluationShiftUnit E M).hom ≫ d⟦(-1 : ℤ)⟧' ≫
      (S.map ((derivedSystemEvaluation B n).map g))⟦(-1 : ℤ)⟧' ≫
        (S.commShiftIso (-1)).inv.app ((derivedSystemEvaluation B n).obj N') =
    E.map f ≫ (((evaluationShiftUnit E M).hom ≫ d⟦(-1 : ℤ)⟧') ≫
      (S.commShiftIso (-1)).inv.app ((derivedSystemEvaluation B n).obj N)) ≫
        S.map (((derivedSystemEvaluation B n).map g)⟦(-1 : ℤ)⟧')
  rw [S.commShiftIso_inv_naturality]
  simp only [Category.assoc]

end SheafOfModules.SequentialDerived.Coinduced
