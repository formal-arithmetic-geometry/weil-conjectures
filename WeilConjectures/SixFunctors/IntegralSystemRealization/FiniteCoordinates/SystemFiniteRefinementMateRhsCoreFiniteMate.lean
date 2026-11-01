/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteIdentityLeftMateCoordinates

/-! # Finite mate conversion after canonical bridge cancellation

Source: Stacks 00YV and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-finite-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] TwoSquare integralCoefficientSheaf
  integralCoefficientCommRingSheaf
  scalarReductionTargetDerived coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientSheafTransition
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  RingHom.ulift
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearProperOpen.derived coefficientSequenceHasDerived coefficientFiniteHasDerived ordinary

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] mateEquiv _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor CategoryTheory.constantSheaf
  AlgebraicGeometry.Scheme.residueField sfIntrinsicExtensionByZero
  sfIntrinsicDerivedEquivalence sfIntrinsicDerivedDirectImageComparison
  sfIntrinsicDerivedPullbackComp push shriek fixedPush fixedShriek
  SemilinearProperOpen.R SemilinearProperOpen.J properOpenMate
  Functor.ofOpSequence Functor.ofSequence
  CanonicalBridge.push CanonicalBridge.shriek CanonicalBridge.pull
  SemilinearProperOpen.sId properOpenAlpha
  derivedUpperStarLowerStarAdjunction
  pullCoordinates pushCoordinates shriekCoordinates

set_option maxRecDepth 4096
set_option Elab.async false

private theorem bridge_cancel
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {X : D} {Y Z : C} (b : X ≅ R.obj Y) (e : Y ≅ Z) :
    b.hom ≫ R.map e.hom ≫ (R.map e.inv ≫ b.inv) = 𝟙 X := by
  rw [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp, Iso.hom_inv_id]

private theorem bridge_cancel_map
    {C D H : Type*} [Category C] [Category D] [Category H] (E : D ⥤ H) (R : C ⥤ D)
    {X : D} {Y Z : C} (b : X ≅ R.obj Y) (e : Y ≅ Z) :
    E.map b.hom ≫ E.map (R.map e.hom) ≫ E.map (R.map e.inv ≫ b.inv) = 𝟙 _ := by
  rw [← E.map_comp, ← E.map_comp, bridge_cancel R b e, E.map_id]

private theorem bridge_cancel_word
    {C D H : Type*} [Category C] [Category D] [Category H] (E : D ⥤ H) (R : C ⥤ D)
    {X : D} {Y Z : C} (b : X ≅ R.obj Y) (e : Y ≅ Z)
    {A B K L : H} (p : A ⟶ B) (q : B ⟶ E.obj X) (s : E.obj X ⟶ K) (t : K ⟶ L) :
    p ≫ q ≫ E.map b.hom ≫ E.map (R.map e.hom) ≫
        E.map (R.map e.inv ≫ b.inv) ≫ s ≫ t = (p ≫ q) ≫ s ≫ t := by
  have h := congrArg (fun v ↦ p ≫ q ≫ v ≫ s ≫ t) (bridge_cancel_map E R b e)
  simpa only [Category.assoc, Category.id_comp] using h

private theorem lift_composite
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {X Y : B} {x y z : A} (a : X ⟶ R.functor.obj x) (b : Y ⟶ R.functor.obj y)
    (p : X ⟶ Y) (s : y ⟶ z) (t : x ⟶ z)
    (h : R.inverse.map p ≫ (R.inverse.map b ≫ (R.unitIso.app y).inv) ≫ s =
      (R.inverse.map a ≫ (R.unitIso.app x).inv) ≫ t) :
    p ≫ b ≫ R.functor.map s = a ≫ R.functor.map t := by
  have hs := R.unitIso.inv.naturality s
  have ht := R.unitIso.inv.naturality t
  dsimp only [Functor.comp_map, Functor.id_map] at hs ht
  apply R.inverse.map_injective
  apply (cancel_mono ((R.unitIso.app z).inv)).1
  simp only [Functor.map_comp, Category.assoc]
  simp only [Iso.app_inv] at *
  rw [hs, ht]
  simpa only [Category.assoc] using h

set_option maxHeartbeats 1000000 in
-- The assembly compares several presentations of the same derived coefficient category.
/-- The evaluated semilinear proper/open mate is the fixed finite mate after the
canonical bridge factors have been removed.

Source: Stacks 00YV and 0F7B; semilinear proper/open mate evaluation.
Apply the evaluated proper/open mate compatibility to the identity-open square,
then expand the source and target coordinate comparisons. The intrinsic
coefficient equivalence unit and counit cancel, leaving the ordinary finite
`properOpenMate` expression. This is functorial and includes identity refinements,
zero inputs, and empty opens.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-finite-mate).
-/
theorem rhsCoreFiniteMate (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ)
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (M : System l E X.obj.left) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let RW := sfIntrinsicDerivedEquivalence d.Z (Padic.coefficientExtensionRing l E (m + 1))
    haveI := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    haveI := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map
          ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
            SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
              X.obj.left).inv.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
          (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.push l E r.hom).hom.app
          ((Operations.shriek l E o c.i).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
          ((z.canonicalBridge.shriek l E c.i).hom.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
          ((z.canonicalBridge.shriek l E c.i).inv.app M) ≫
          (z.canonicalBridge.push l E r.hom).inv.app
            ((Operations.shriek l E o c.i).obj M)) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) =
    (shriek l E o m d.i M).hom ≫
      RW.functor.map
        ((ProperOpenShriek A d.i).map
          (((ordinary D A).sId X).inv.app (input l E m X.obj.left M)) ≫
          (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app
              (input l E m X.obj.left M)) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
  let RW := sfIntrinsicDerivedEquivalence d.Z
    (Padic.coefficientExtensionRing l E (m + 1))
  let _ := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let _ := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  let η : Operations.push l E o (𝟙 X.obj.left) ≅ 𝟭 (System l E X.obj.left) :=
    z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
    SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X.obj.left
  let Ji := ProperOpenShriek A d.i
  let sid := (ordinary D A).sId X
  have hfixed := identityLeftMateCoordinates l E D o z m X c.i r.hom d.i
    (r.i_hom.trans (Category.id_comp _).symm) M
  dsimp only at hfixed
  have h := lift_composite RW (shriek l E o m d.i M).hom
    (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom
    ((coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map (η.inv.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
          (r.i_hom.trans (Category.id_comp _).symm)).app M))
    ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom)
    (Ji.map (sid.inv.app (input l E m X.obj.left M)) ≫
      (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
        (r.i_hom.trans (Category.id_comp _).symm)).app (input l E m X.obj.left M))
    (by simpa only [A, RW, fixedEvaluation_map, fixedEvaluation_obj, Functor.id_obj,
      fixedPush, fixedShriek, Functor.comp_map,
      Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using hfixed)
  let R : System l E c.Z ⥤ System l E d.Z :=
    SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom
  exact (bridge_cancel_word (coefficientSequenceDerivedEvaluation l E d.Z m) R
    ((z.canonicalBridge.push l E r.hom).app ((Operations.shriek l E o c.i).obj M))
    ((z.canonicalBridge.shriek l E c.i).app M)
    ((coefficientSequenceDerivedEvaluation l E d.Z m).map
      ((Operations.shriek l E o d.i).map (η.inv.app M)))
    ((coefficientSequenceDerivedEvaluation l E d.Z m).map
      ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
        (r.i_hom.trans (Category.id_comp _).symm)).app M))
    (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom
    (RW.functor.map ((ProperOpenPush A r.hom).map
      (fixedShriek l E o m c.i M).hom))).trans h

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
