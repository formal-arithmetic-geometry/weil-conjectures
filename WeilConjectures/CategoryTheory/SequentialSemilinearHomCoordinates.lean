/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedProducts
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Actual shifted Hom coordinates of the coinduced products

Source: Stacks 0145, 015F and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe a av d dv u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Precomposition with an isomorphism, additively.
Source: Stacks 0145 (blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def precomposeIsoAddEquiv {A : Type a} [Category.{av} A] [Preadditive A]
    {X Y : A} (e : X ≅ Y) (Z : A) : (Y ⟶ Z) ≃+ (X ⟶ Z) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' _ _ := by simp only [Preadditive.comp_add]

/-- Postcomposition with an isomorphism, additively.
Source: Stacks 0145 (blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def postcomposeIsoAddEquiv {A : Type a} [Category.{av} A] [Preadditive A]
    (X : A) {Y Z : A} (e : Y ≅ Z) : (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- The canonical source-shift identification after evaluation.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def evaluationShiftUnit
    {A : Type a} [Category.{av} A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [HasShift D ℤ]
    (E : A ⥤ D) [E.CommShift ℤ] (M : A) :
    E.obj M ≅ (E.obj (M⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧ :=
  E.mapIso ((shiftFunctorCompIsoId A (1 : ℤ) (-1) (by decide)).symm.app M) ≪≫
    (E.commShiftIso (-1)).app (M⟦(1 : ℤ)⟧)

/-- Move the source shift through an exact evaluation and across Hom.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def evaluationSourceShiftHomEquiv
    {A : Type a} [Category.{av} A] [Preadditive A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (E : A ⥤ D) [E.CommShift ℤ] (M : A) (Y : D) :
    (E.obj (M⟦(1 : ℤ)⟧) ⟶ Y) ≃+ (E.obj M ⟶ Y⟦(-1 : ℤ)⟧) :=
  (show (E.obj (M⟦(1 : ℤ)⟧) ⟶ Y) ≃+
      ((E.obj (M⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧ ⟶ Y⟦(-1 : ℤ)⟧) from
    { toEquiv := (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor D (-1 : ℤ))).homEquiv
      map_add' _ _ := (shiftFunctor D (-1 : ℤ)).map_add }).trans
    (precomposeIsoAddEquiv (evaluationShiftUnit E M) _)

/-- The shift identification is natural in the source.
Source: Stacks 0145
(blueprint: def-sf-sequential-semilinear-hom-coordinates).
Proof: use naturality of the shift-equivalence unit, followed by naturality of the
canonical evaluation-shift comparison. -/
theorem evaluationShiftUnit_natural
    {A : Type a} [Category.{av} A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [HasShift D ℤ]
    (E : A ⥤ D) [E.CommShift ℤ] {M M' : A} (f : M' ⟶ M) :
    E.map f ≫ (evaluationShiftUnit E M).hom =
      (evaluationShiftUnit E M').hom ≫ (E.map (f⟦(1 : ℤ)⟧'))⟦(-1 : ℤ)⟧' := by
  dsimp only [evaluationShiftUnit, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  have hu := (shiftFunctorCompIsoId A (1 : ℤ) (-1) (by decide)).inv.naturality f
  change f ≫ _ = _ ≫ (f⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' at hu
  rw [← E.map_comp_assoc, hu, E.map_comp, Category.assoc,
    E.commShiftIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

/-- The forward coordinate map is the shifted morphism after the canonical source unit.
Source: Stacks 0145
(blueprint: def-sf-sequential-semilinear-hom-coordinates).
Proof: this is the definition of the two additive equivalences being composed. -/
theorem evaluationSourceShiftHomEquiv_apply
    {A : Type a} [Category.{av} A] [Preadditive A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (E : A ⥤ D) [E.CommShift ℤ] (M : A) (Y : D)
    (b : E.obj (M⟦(1 : ℤ)⟧) ⟶ Y) :
    evaluationSourceShiftHomEquiv E M Y b =
      (evaluationShiftUnit E M).hom ≫ b⟦(-1 : ℤ)⟧' := rfl

/-- The source-shift identification respects transformations commuting with shifts.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates).
Proof: use shift compatibility at M[1], then naturality at the shift-equivalence unit. -/
theorem evaluationShiftUnit_transformation
    {A : Type a} [Category.{av} A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [HasShift D ℤ]
    {E F : A ⥤ D} [E.CommShift ℤ] [F.CommShift ℤ]
    (t : E ⟶ F) [NatTrans.CommShift t ℤ] (M : A) :
    (evaluationShiftUnit E M).hom ≫ (t.app (M⟦(1 : ℤ)⟧))⟦(-1 : ℤ)⟧' =
      t.app M ≫ (evaluationShiftUnit F M).hom := by
  dsimp only [evaluationShiftUnit, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc]
  have ht := t.naturality
    ((shiftFunctorCompIsoId A (1 : ℤ) (-1) (by decide)).inv.app M)
  exact (congrArg (fun z ↦ z ≫ (F.commShiftIso (-1)).hom.app (M⟦(1 : ℤ)⟧)) ht).trans
    (Category.assoc _ _ _)

/-- Moving a source shift through a composite functor is compatible with its shift comparison.
Source: Stacks 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates).
Proof: expand the composite shift comparison; naturality of the second comparison
moves the shifted map across it, and the inverse comparison cancels. -/
theorem evaluationShiftUnit_composite
    {A : Type a} [Category.{av} A] [HasShift A ℤ]
    {D : Type d} [Category.{dv} D] [HasShift D ℤ]
    {D' : Type u} [Category.{v} D'] [HasShift D' ℤ]
    (E : A ⥤ D) (S : D ⥤ D') [E.CommShift ℤ] [S.CommShift ℤ]
    (M : A) {Y : D} (b : E.obj (M⟦(1 : ℤ)⟧) ⟶ Y) :
    (evaluationShiftUnit (E ⋙ S) M).hom ≫ (S.map b)⟦(-1 : ℤ)⟧' ≫
      (S.commShiftIso (-1)).inv.app Y =
        S.map ((evaluationShiftUnit E M).hom ≫ b⟦(-1 : ℤ)⟧') := by
  dsimp only [evaluationShiftUnit, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map, Functor.comp_obj, Iso.symm_hom]
  rw [Functor.commShiftIso_comp_hom_app]
  simp only [Category.assoc, Functor.map_comp]
  rw [← S.commShiftIso_hom_naturality_assoc b (-1)]
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

end CategoryTheory

namespace SheafOfModules.SequentialDerived.Coinduced
open Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The degree-zero vertex coordinates use the prescribed identification with shift zero.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def vertexCoordinatesZero (M N : DerivedCategory (StrictRingSystem B)) :
    (M ⟶ product B N) ≃+ vertexHom B M N 0 :=
  (productHomEquiv B M N).trans (AddEquiv.piCongrRight fun n ↦
    postcomposeIsoAddEquiv _
      ((shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).app
        ((derivedSystemEvaluation B n).obj N)).symm)

/-- The degree-zero edge coordinates shift before restricting scalars.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def edgeCoordinatesZero (M N : DerivedCategory (StrictRingSystem B)) :
    (M ⟶ relations B N) ≃+ edgeHom B M N 0 :=
  (relationsHomEquiv B M N).trans (AddEquiv.piCongrRight fun n ↦
    postcomposeIsoAddEquiv _ ((adjacentRestriction B n).mapIso
      ((shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).app
        ((derivedSystemEvaluation B n).obj N)).symm))

/-- Negative-degree vertex coordinates are ordinary Hom with source shifted once.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def vertexCoordinatesNeg (M N : DerivedCategory (StrictRingSystem B)) :
    (M⟦(1 : ℤ)⟧ ⟶ product B N) ≃+ vertexHom B M N (-1) :=
  (productHomEquiv B (M⟦(1 : ℤ)⟧) N).trans (AddEquiv.piCongrRight fun n ↦
    evaluationSourceShiftHomEquiv (derivedSystemEvaluation B n) M
      ((derivedSystemEvaluation B n).obj N))

/-- Negative-degree edge coordinates use the canonical restriction-shift comparison.
Source: Stacks 0145, 015F
(blueprint: def-sf-sequential-semilinear-hom-coordinates). -/
def edgeCoordinatesNeg (M N : DerivedCategory (StrictRingSystem B)) :
    (M⟦(1 : ℤ)⟧ ⟶ relations B N) ≃+ edgeHom B M N (-1) :=
  (relationsHomEquiv B (M⟦(1 : ℤ)⟧) N).trans (AddEquiv.piCongrRight fun n ↦
    (evaluationSourceShiftHomEquiv (derivedSystemEvaluation B (n + 1)) M
      ((adjacentRestriction B n).obj ((derivedSystemEvaluation B n).obj N))).trans
      (postcomposeIsoAddEquiv _
        (((adjacentRestriction B n).commShiftIso (-1)).symm.app
          ((derivedSystemEvaluation B n).obj N))))

/-- The zero-degree vertex coordinates of the augmentation are the specified evaluation.
Source: Stacks 015F, 0941
(blueprint: def-sf-sequential-semilinear-hom-coordinates).
Proof: transpose each projection of the augmentation by its adjunction, then insert
exactly the prescribed shift-zero identification. -/
theorem vertexCoordinatesZero_augmentation
    {M N : DerivedCategory (StrictRingSystem B)} (f : M ⟶ N) :
    vertexCoordinatesZero B M N (f ≫ augmentation B N) = evaluateHom B M N f := by
  funext n
  have h := congrFun (CoinducedSequence.productHomEquiv_augmentation
    (derivedSystemEvaluation B) (derivedRight B) (derivedAdjunction B) f) n
  exact congrArg (fun z ↦ z ≫
    (shiftFunctorZero (DerivedCategory (systemLevel B n)) ℤ).inv.app
      ((derivedSystemEvaluation B n).obj N)) h

end SheafOfModules.SequentialDerived.Coinduced
