/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCyclicAugmentationZero
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientTargetShiftLemmas
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCyclicAugmentationZero

/-! # Shift compatibility of the cyclic quotient augmentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local semireducible] cyclicDiscreteRestriction

/-- The derived scalar extension adjunction, with left adjoint `derivedScalars`. -/
def derivedScalarsAdjunction
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    derivedScalars a X ⊣ (Mod.comap (D := DiagonalAb X) (coefficientMap a X)).mapDerivedCategory :=
  @Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj Λ X) (condensedRingObj Λ' X) _ _
    (isCommMonObj_condensedRingObj Λ X) (isCommMonObj_condensedRingObj Λ' X)
    (coefficientMap a X) _

instance derivedScalarsAdjunction_commShift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    (derivedScalarsAdjunction a X).CommShift ℤ :=
  (@Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj Λ X) (condensedRingObj Λ' X) _ _
    (isCommMonObj_condensedRingObj Λ X) (isCommMonObj_condensedRingObj Λ' X)
    (coefficientMap a X) _).commShift_of_rightAdjoint ℤ

/-- The underlying scalar unit, written with the left unitor so that its source carries
the canonical shift of the forgetful functor. -/
theorem scalarUnderlyingUnit_eq
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    scalarUnderlyingUnit a X =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (derivedScalarsAdjunction a X).unit
          (Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X)).mapDerivedCategory ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (derivedScalars a X)
          (Functor.mapDerivedCategoryCompIso
            (Mod.comap (D := DiagonalAb X) (coefficientMap a X))
            (Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X))).hom := by
  ext M
  simp only [scalarUnderlyingUnit, derivedScalarsAdjunction, derivedScalars,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp]
  congr 1
  exact Category.comp_id _

instance scalarUnderlyingUnit_commShift
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    NatTrans.CommShift (scalarUnderlyingUnit a X) ℤ := by
  rw [scalarUnderlyingUnit_eq]
  exact (inferInstance : NatTrans.CommShift ((Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (derivedScalarsAdjunction a X).unit
      (Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X)).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (derivedScalars a X)
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (D := DiagonalAb X) (coefficientMap a X))
        (Mod.forget (D := DiagonalAb X) (condensedRingObj Λ X))).hom) ℤ)

/-- The cyclic augmentation as an explicit composite of shift-compatible transformations. -/
def cyclicAugmentationComposite (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    (diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategory ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory ⟶
      (eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y)) ⋙
        (p.eW.F.mapDerivedCategory ⋙
          (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory ⋙
            (diagonalForget l (diagonalSurface Y)).mapDerivedCategory) :=
  ((Functor.mapDerivedCategoryCompIso
      (diagonalCompletedRestriction l (diagonalSurface Y))
      (diagonalForget l (diagonalSurface Y))) ≪≫
    Functor.mapDerivedCategoryNatIso eW.underlying.symm ≪≫
    (Functor.mapDerivedCategoryCompIso eW.F
      (Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
        (diagonalSurface Y)))).symm).hom ≫
  Functor.whiskerLeft eW.F.mapDerivedCategory
    (scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerLeft (eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y))
    (Functor.isoWhiskerLeft p.eW.F.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso
          (diagonalFiniteToPadic l n (diagonalSurface Y))
          (diagonalForget l (diagonalSurface Y))) ≪≫
      (Functor.mapDerivedCategoryCompIso p.eW.F
        (diagonalFiniteToPadic l n (diagonalSurface Y) ⋙
          diagonalForget l (diagonalSurface Y))) ≪≫
      Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)).inv

theorem cyclicAugmentationComposite_app (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n)
    (X : DerivedCategory (DiagonalCompleted l (diagonalSurface Y))) :
    (cyclicEvaluationAugmentation l Y n eW p).app X =
      (cyclicAugmentationComposite l Y n eW p).app X := by
  rw [cyclic_augmentation_app]
  simp only [cyclicAugmentationComposite, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp]
  rfl

instance cyclicAugmentationComposite_commShift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    NatTrans.CommShift (cyclicAugmentationComposite l Y n eW p) ℤ := by
  unfold cyclicAugmentationComposite
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_comp]
  infer_instance

/-- The cyclic augmentation commutes with shifts, for the composite shift structures of
its source and target functors. -/
theorem cyclicEvaluationAugmentation_shift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n)
    (X : DerivedCategory (DiagonalCompleted l (diagonalSurface Y))) (a : ℤ) :
    (cyclicEvaluationAugmentation l Y n eW p).app (X⟦a⟧) =
      (((diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategory ⋙
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory).commShiftIso a).hom.app X ≫
      ((cyclicEvaluationAugmentation l Y n eW p).app X)⟦a⟧' ≫
      (((eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y)) ⋙
        (p.eW.F.mapDerivedCategory ⋙
          (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory ⋙
            (diagonalForget l (diagonalSurface Y)).mapDerivedCategory)).commShiftIso a).inv.app
        X := by
  rw [cyclicAugmentationComposite_app, cyclicAugmentationComposite_app]
  exact NatTrans.app_shift _ a X

/-- The shifted cyclic target, unfolded to the completed and finite target composites. -/
theorem cyclicEvaluationTarget_eq_completed (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicEvaluationTarget l Y n eW p =
      completedFunctorTarget eW.F (derivedScalars (cyclicMap l n) (diagonalSurface Y) ⋙
        p.eW.F.mapDerivedCategory ⋙
          (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory) 2 eW.lineIso
        (threeFunctorTarget (derivedScalars (cyclicMap l n) (diagonalSurface Y)) p.eW.F
          (diagonalFiniteToPadic l n (diagonalSurface Y)) 2
          (((derivedScalars (cyclicMap l n) (diagonalSurface Y)).commShiftIso
            ((2 : ℕ) : ℤ)).hom.app _ ≫ p.line.iso.hom⟦((2 : ℕ) : ℤ)⟧')
          p.lineEndpoint.iso) := rfl

/-- The unshifted cyclic target, unfolded to the exact realization composite. -/
theorem cyclicEvaluationTargetZero_eq (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicEvaluationTargetZero l Y n eW p =
      exactRealizationTargetZero eW.F (derivedScalars (cyclicMap l n) (diagonalSurface Y))
        p.eW.F (diagonalFiniteToPadic l n (diagonalSurface Y)) eW.lineIso.hom p.line.iso.hom
        p.lineEndpoint.iso.hom := rfl

/-- The shifted cyclic target is the shift of the unshifted cyclic target. -/
theorem cyclicEvaluationTarget_eq_shift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicEvaluationTarget l Y n eW p =
      ((eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) (diagonalSurface Y) ⋙
        p.eW.F.mapDerivedCategory ⋙
          (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory).commShiftIso
            (2 : ℤ)).hom.app _ ≫
        (cyclicEvaluationTargetZero l Y n eW p)⟦(2 : ℤ)⟧' := by
  rw [cyclicEvaluationTarget_eq_completed, cyclicEvaluationTargetZero_eq]
  exact completedFunctorTarget_eq_shift eW.F (derivedScalars (cyclicMap l n) (diagonalSurface Y))
    p.eW.F (diagonalFiniteToPadic l n (diagonalSurface Y)) 2 eW.lineIso p.line.iso
    p.lineEndpoint.iso

/-- The cyclic augmentation followed by the shifted cyclic target is the shift of the
augmentation followed by the unshifted target. -/
theorem cyclicEvaluationAugmentation_targetShift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (n : ℕ) [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    (cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedCodomain l Y) ≫
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
          (cyclicEvaluationTarget l Y n eW p) =
      (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
          (((diagonalCompletedRestriction l (diagonalSurface Y)).mapDerivedCategory.commShiftIso
            (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.purTwistZlModule (diagonalSurface Y) l))) ≫
        ((diagonalForget l (diagonalSurface Y)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          _ ≫
        ((cyclicEvaluationAugmentation l Y n eW p).app
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.purTwistZlModule (diagonalSurface Y) l)) ≫
          (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
            (cyclicEvaluationTargetZero l Y n eW p))⟦(2 : ℤ)⟧' ≫
        ((diagonalForget l (diagonalSurface Y)).mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app
          _ := by
  let W := diagonalSurface Y
  let U := (diagonalForget l W).mapDerivedCategory
  let X₀ := (DerivedCategory.singleFunctor (DiagonalCompleted l W) 0).obj
    (Scheme.purTwistZlModule W l)
  let C' := eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) W ⋙
    p.eW.F.mapDerivedCategory ⋙ (diagonalFiniteToPadic l n W).mapDerivedCategory
  let Fc := (eW.F.mapDerivedCategory ⋙ derivedScalars (cyclicMap l n) W) ⋙
    (p.eW.F.mapDerivedCategory ⋙ (diagonalFiniteToPadic l n W).mapDerivedCategory ⋙ U)
  have hΦ : (Fc.commShiftIso (2 : ℤ)).hom.app X₀ =
      U.map ((C'.commShiftIso (2 : ℤ)).hom.app X₀) ≫
        (U.commShiftIso (2 : ℤ)).hom.app (C'.obj X₀) := by
    simp only [Fc, C', Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
      Category.assoc]
    rfl
  have hΦ' : (Fc.commShiftIso (2 : ℤ)).inv.app X₀ ≫
      U.map ((C'.commShiftIso (2 : ℤ)).hom.app X₀) =
        (U.commShiftIso (2 : ℤ)).inv.app (C'.obj X₀) := by
    rw [← cancel_mono ((U.commShiftIso (2 : ℤ)).hom.app (C'.obj X₀)), Category.assoc, ← hΦ,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  rw [cyclicEvaluationAugmentation_shift, cyclicEvaluationTarget_eq_shift]
  rw [Functor.commShiftIso_comp_hom_app]
  exact augmented_shift_comp (diagonalForget l (diagonalSurface Y)).mapDerivedCategory
    ((C'.commShiftIso (2 : ℤ)).hom.app X₀) (cyclicEvaluationTargetZero l Y n eW p)
    _ _ _ _ hΦ'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
