/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.FiniteNativeAlphaCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Native.IntegralNativePullEvaluation
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import WeilConjectures.CategoryTheory.Derived.DerivedEquivalenceCancellation

/-! # Native evaluation coordinates for system operations

Source: Stacks 00YV, 03DI and 07A7; finite coefficient realization in
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-native-operation-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf presheafToSheaf Functor.leftAdjoint
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportSystemLevel compactSupportSystemQuotient

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible] Equivalence.mapDerivedCategory sfIntrinsicDerivedEquivalence
attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Functor.mapHomologicalComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluate native pullback and then cancel the coefficient presentation.
Source: Stacks 03DI and 07A7; finite evaluation in prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-native-operation-coordinates). -/
def systemNativePullCoordinates (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ⋙ fixedEvaluation l E m X ≅
      fixedEvaluation l E m Y ⋙
        ProperOpenPull (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f :=
  Functor.isoWhiskerRight (integralNativePullIso l E f) (fixedEvaluation l E m X) ≪≫
    Functor.isoWhiskerRight
      (VaryingRing.evalG (scalarRings l E) (scalarTransitions l E) f m)
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (m + 1))).inverse ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E Y m)
      (finiteNativePullCoordinates (Padic.coefficientExtensionRing l E (m + 1)) f)

/-- Evaluate native open extension and then cancel the coefficient presentation.
Source: Stacks 03DI and 07A7; finite evaluation in prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-native-operation-coordinates). -/
def systemNativeShriekCoordinates (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Operations.shriek l E o j ⋙ fixedEvaluation l E m Y ≅
      fixedEvaluation l E m X ⋙
        ProperOpenShriek (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) j :=
  Functor.isoWhiskerRight (integralNativeOpenIso l E j (o.extension j))
      (fixedEvaluation l E m Y) ≪≫
    Functor.isoWhiskerRight
      (VaryingRing.evalJ (scalarRings l E) (scalarTransitions l E) j m)
      (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (m + 1))).inverse ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E X m)
      (finiteNativeShriekCoordinates (Padic.coefficientExtensionRing l E (m + 1)) j)

private theorem native_coordinate_formula (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : System l E Y) :
    let A := Padic.coefficientExtensionRing l E (m + 1)
    let RX := sfIntrinsicDerivedEquivalence X A
    let RY := sfIntrinsicDerivedEquivalence Y A
    let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    let o := Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence Y A).inverse
        (L ⋙ (sfIntrinsicModuleEquivalence X A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
    (systemNativePullCoordinates l E m f).hom.app M =
      RX.inverse.map ((pullbackTensorDerivedEvaluation l E f m).hom.app M ≫
        o.hom.app ((coefficientSequenceDerivedEvaluation l E Y m).obj M)) ≫
      RX.unitIso.inv.app (L.mapDerivedCategory.obj
        (RY.inverse.obj ((coefficientSequenceDerivedEvaluation l E Y m).obj M))) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).inv.app
          (RY.inverse.obj ((coefficientSequenceDerivedEvaluation l E Y m).obj M)) := by
  dsimp only
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let N := (coefficientSequenceDerivedEvaluation l E Y m).obj M
  let q := openSquarePullbackModel A f
  let δ := Functor.isoWhiskerRight q EX.inverse ≪≫
    Functor.isoWhiskerLeft EY.inverse (Functor.isoWhiskerLeft L EX.unitIso.symm) ≪≫
    Functor.isoWhiskerLeft EY.inverse (Functor.rightUnitor L)
  let o := Functor.mapDerivedCategoryCompIso EY.inverse (L ⋙ EX.functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L EX.functor)
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  have hc := congr_app (Functor.mapDerivedCategory_cancelEquivalence EY.inverse L EX
    (proEtaleConstantRingPullback A f) q) N
  have hn := integralNativePullEvaluation l E f m M
  calc
    _ = RX.inverse.map ((coefficientSequenceDerivedEvaluation l E X m).map
          ((integralNativePullIso l E f).hom.app M)) ≫
        RX.inverse.map ((VaryingRing.evalG (scalarRings l E)
          (scalarTransitions l E) f m).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso δ).hom.app N ≫
        e.inv.app (RY.inverse.obj N) := rfl
    _ = RX.inverse.map (((coefficientSequenceDerivedEvaluation l E X m).map
          ((integralNativePullIso l E f).hom.app M) ≫
        (VaryingRing.evalG (scalarRings l E) (scalarTransitions l E) f m).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso q).hom.app N) ≫ o.hom.app N) ≫
        RX.unitIso.inv.app (L.mapDerivedCategory.obj (RY.inverse.obj N)) ≫
        e.inv.app (RY.inverse.obj N) := by
      rw [hc]
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.map_comp, Category.assoc]
      rfl
    _ = _ := congrArg (fun t ↦ RX.inverse.map (t ≫ o.hom.app N) ≫
      RX.unitIso.inv.app (L.mapDerivedCategory.obj (RY.inverse.obj N)) ≫
      e.inv.app (RY.inverse.obj N)) hn

/-- Native pull evaluation has the prescribed adjunction coordinate.

Source: Stacks 03DI, 07A7 and 0941; the pull-adjunction normalization step of
lem-sf-system-finite-alpha-coordinates.
Proof: first use exact-localization equivalence cancellation and
integralNativePullEvaluation to write the native pull coordinate in fixed
realization coordinates. Apply pullCoordinates_existsUnique. Its defining mate
equation becomes a counit equation by mateEquiv_counit, and precomposition by the
native pull isomorphism cancels its inverse. The existing arbitrary-scheme
intrinsicDerivedCounit_coordinates and coordinate_counit_comp transport the
intrinsic counit through the coefficient equivalences and the exact/left-derived
pull comparison. The system evaluation counit equation finishes the calculation.
Identity maps, empty schemes and zero systems use the same equations. No
proper/open square or alpha occurs here.
(blueprint: lem-sf-system-native-operation-coordinates). -/
theorem systemNativeOperationCoordinates (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullCoordinates l E o m f = systemNativePullCoordinates l E m f := by
  apply (pullCoordinates_existsUnique l E o m f).unique
    (pullCoordinates_mate l E o m f)
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Pf := ProperOpenPull (ULift.{u + 1} A) f
  let R := ProperOpenPush (ULift.{u + 1} A) f
  let P := finiteDerivedPullback l E m f
  let Ri := proEtaleConstantDerivedDirectImage f A
  let a := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    ).mapDerivedCategoryRightDerivedAdjunction
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let q := Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence Y A).inverse
      (L ⋙ (sfIntrinsicModuleEquivalence X A).functor) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  let ν := sfIntrinsicDerivedDirectImageComparison f A
  have ha (K) : a.counit.app K = e.inv.app (R.obj K) ≫ b.counit.app K := by
    exact congrArg (fun z ↦ z.counit.app K) (exactProEtaleAdjunction_eq A f)
  ext M
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((systemNativePullCoordinates l E m f).hom.app
    ((Operations.push l E o f).obj M))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  have ht := coordinate_counit_comp RY RX L.mapDerivedCategory Pf R P Ri a b
    (finiteAdj l E f m) e q ν ha
    ((coefficientSequenceDerivedEvaluation l E X m).obj M)
    ((coefficientSequenceDerivedEvaluation l E Y m).obj
      ((Operations.push l E o f).obj M))
    ((coefficientSequenceDerivedEvaluation l E X m).obj
      ((pull l E f).obj ((Operations.push l E o f).obj M)))
    ((pullbackTensorDerivedEvaluation l E f m).hom.app
      ((Operations.push l E o f).obj M))
    (((o.evaluation f).evaluation m).hom.app M)
    (intrinsicDerivedCounit_coordinates A f
      ((coefficientSequenceDerivedEvaluation l E X m).obj M))
  rw [(o.evaluation f).counit m M] at ht
  rw [native_coordinate_formula]
  simpa only [pushCoordinates, fixedPush, push, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, NatIso.ofComponents_hom_app,
    Functor.map_comp, Functor.comp_map, Category.assoc, fixedEvaluation_map, input,
    A, RX, RY, L, Pf, R, P, Ri, a, b, e, q, ν,
    Equivalence.unitInv, Equivalence.counitInv, fixedEvaluation, Functor.comp_obj,
    Functor.id_obj, ProperOpenPull] using ht.symm

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
