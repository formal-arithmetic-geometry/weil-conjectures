/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import all WeilConjectures.PoincareDuality.Pod.PodNativeRoosFunctorComparison
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.PoincareDuality.Pod.PodNormalizedRoosComparisonShift
import all WeilConjectures.PoincareDuality.Pod.PodStrictRoosReindexShift
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import all WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Signed shifts of the normalized whole-tower limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 10000] WeilConjectures.podLimitCommShift

attribute [local instance 50000] WeilConjectures.podSheafCanonicalPreadditive

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep the coefficient universe explicit during sheafification synthesis.
private instance (priority := 20000) fixedAbSheafify (Z : Scheme.{u}) :
    HasSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Z

private instance (priority := 20000) fixedAbBijective (Z : Scheme.{u}) :
    (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Z

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option maxHeartbeats 800000 in
-- The calculation pastes several strict and localized shift squares.
/-- The normalized whole-tower limit reindexing commutes with integer shifts.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941 and 011G
(blueprint: lem-pod-reindexing-limit-signed-shift-s8).

Proof: the restricted generator formula gives the same termwise map in degree i+r
before and after shifting; hence its restriction comparison commutes with shift.
Use naturality and the RoosShift law to paste this strict-tower square with the
source and target signed Roos comparisons. The two normalized limit-to-Roos
identities then turn LimitModel into the shift square for D.limit at Q(C).
Cancel the invertible Roos and localization comparisons. Finally the essential
surjectivity of Q and naturality extend the identity to all derived objects. -/
theorem podReindexingLimitSignedShift
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hnat : PodCompletionReindex.RoosNaturality l E g D)
    (hshift : PodCompletionReindex.RoosShift l E g D)
    (hgen : PodCompletionReindex.RestrictedGenerators l E g D)
    (hmodel : PodCompletionReindex.LimitModel l E g D)
    (hSY : D.shiftSource.Laws) (hSX : D.shiftTarget.Laws) :
    NatTrans.CommShift D.limit.hom ℤ := by
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E Y)
  let := CategoryTheory.RoosConeCalculus.roosCommShift
    (A := scalarReductionSource l E X)
  let RY := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
  let RX := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let P := (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
  let F := isoReductionIntegralComplex l E g
  let HY := RY ⋙ roosF
  let HX := RX ⋙ roosF
  let U := HY ⋙ F
  let V := P ⋙ HX
  obtain ⟨a, b, ha, hb, haC, hbC⟩ := podReindexingLimitPresentations l E g D
  let ν := a.symm ≪≫ Functor.isoWhiskerLeft (coefficientQ l E Y) D.limit ≪≫ b
  let f (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      U.obj C ⟶ V.obj C := (D.roos (podRestrictedTower l E C)).hom ≫
        integralOperationsRoosFunctor.map (D.restricted C).hom
  have hnC (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
      ν.hom.app C = DerivedCategory.Q.map (f C) := by
    apply (cancel_epi (a.hom.app C)).mp
    dsimp only [ν, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [Iso.hom_inv_id_app_assoc]
    rw [haC, hbC]
    dsimp only [f]
    erw [DerivedCategory.Q.map_comp]
    erw [Category.assoc]
    exact (hmodel C).symm
  have hf (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (r : ℤ) :
      (U.commShiftIso r).hom.app C ≫ (f C)⟦r⟧' =
        f (C⟦r⟧) ≫ (V.commShiftIso r).hom.app C :=
    podReindexingStrictNativeShift l E g D hnat hshift hgen hSY hSX C r
  have : NatTrans.CommShift ν.hom ℤ := commShift_Q_components U V ν.hom f hnC hf
  have : NatTrans.CommShift (Functor.whiskerLeft (coefficientQ l E Y) D.limit.hom) ℤ :=
    commShift_of_conjugate a b _ ν.hom (by
      dsimp only [ν, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp])
  exact NatTrans.CommShift.of_whiskerLeft D.limit.hom (coefficientQ l E Y)
    (fun A ↦ ⟨DerivedCategory.Q.objPreimage A,
      (DerivedCategory.Q.objObjPreimageIso A).inv, inferInstance⟩)

end WeilConjectures
