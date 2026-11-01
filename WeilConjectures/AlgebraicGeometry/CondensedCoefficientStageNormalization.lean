/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Exact.ExactDerivedTransformation

/-! # Normalized scalar extensions for condensed constructible coefficients

Source: latest blueprint, `sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/`,
opening scalar-extension paragraph and `def-sfb-derived-extend-comp-iso.proof.md`;
`sk-prop-qlbar-two-colimit/def-sfb-constructible-cocone.md`.
(blueprint: lem-general-algebraically-closed-coefficient-stages).

The categories and scalar functors are the existing condensed ones. The structure below
packages their normalized shifts, unitors and associators. Its vertex comparison is the
existing comparison of the constructible cocone. Exactness is expressed by preservation
of ambient distinguished triangles, which is precisely exactness for the induced
triangulated structures, without choosing a second pretriangulation on a full subcategory.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.upperStarFromPointComp
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_pointUpperStar
  AlgebraicGeometry.ProEtale.oplaxMonoidal_pointUpperStar

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The fixed comparison with degreewise scalar extension followed by localization.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact scalar extension.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def finiteScalarLocalizationIso {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    DerivedCategory.Q ⋙ derivedExtendScalarsSubfield X ℓ h ≅
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategoryFactors

/-- The corresponding fixed comparison for extension to the condensed algebraic closure.
Source: blueprint `def-sfb-derived-extend-comp-iso.proof.md`, exact scalar extension.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def closureScalarLocalizationIso (E : FiniteIntermediateField ℓ) :
    DerivedCategory.Q ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (Mod.extendScalars
        (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategoryFactors

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- Shift and comparison data on the fixed condensed scalar functors. Category shifts
are the restrictions of ordinary derived shifts, using `ObjectProperty.hasShift`.
Normalization and coherence are propositions about these data, stated separately below.
The larger heartbeat budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
class CondensedCoefficientStageData where
  /-- The finite coefficient subcategories are stable under every integer shift. -/
  [finiteStable : ∀ E : FiniteIntermediateField ℓ,
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsStableUnderShift ℤ]
  /-- The vertex is stable under every ordinary derived shift. -/
  [closureStable : (boundedConstructible (padicAlgClRingObj X ℓ)).IsStableUnderShift ℤ]
  /-- Coherent shifts on the ambient finite scalar functors. -/
  [ambientFiniteShift : ∀ (E F : FiniteIntermediateField ℓ) (h : E ≤ F),
    (derivedExtendScalarsSubfield X ℓ h).CommShift ℤ]
  /-- Coherent shifts on the ambient vertex scalar functors. -/
  [ambientClosureShift : ∀ E : FiniteIntermediateField ℓ,
    (derivedExtendScalarsToPadicAlgCl X ℓ E).CommShift ℤ]
  /-- Coherent shift comparisons on the restricted finite scalar functors. -/
  [finiteShift : ∀ (E F : FiniteIntermediateField ℓ) (h : E ≤ F),
    (constructibleExtendScalars X ℓ h).CommShift ℤ]
  /-- Coherent shift comparisons on the restricted vertex scalar functors. -/
  [closureShift : ∀ E : FiniteIntermediateField ℓ,
    (constructibleToPadicAlgCl X ℓ E).CommShift ℤ]
  /-- Identity coefficient inclusions, used only to type the ordinary unit normalization. -/
  coefficientId (E : FiniteIntermediateField ℓ) :
    padicSubfieldRingObjMap X ℓ (le_refl E) = 𝟙 (padicSubfieldRingObj X ℓ E)
  /-- Composition of coefficient inclusions, used to type tensor multiplication. -/
  coefficientComp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    padicSubfieldRingObjMap X ℓ h ≫ padicSubfieldRingObjMap X ℓ k =
      padicSubfieldRingObjMap X ℓ (h.trans k)
  /-- Ambient unit comparison. -/
  ambientUnit (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsSubfield X ℓ (le_refl E) ≅ 𝟭 _
  /-- Ambient finite composition comparison. -/
  ambientComp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsSubfield X ℓ k ≅
      derivedExtendScalarsSubfield X ℓ (h.trans k)
  /-- Unit comparison on the actual bounded constructible category. -/
  unit (E : FiniteIntermediateField ℓ) :
    constructibleExtendScalars X ℓ (le_refl E) ≅ 𝟭 (PadicSubfieldConstructible X ℓ E)
  /-- Composition comparison on the actual bounded constructible categories. -/
  comp (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    constructibleExtendScalars X ℓ h ⋙ constructibleExtendScalars X ℓ k ≅
      constructibleExtendScalars X ℓ (h.trans k)

attribute [instance_reducible] CondensedCoefficientStageData.ambientFiniteShift
  CondensedCoefficientStageData.ambientClosureShift CondensedCoefficientStageData.finiteShift
  CondensedCoefficientStageData.closureShift

attribute [instance] CondensedCoefficientStageData.finiteStable
  CondensedCoefficientStageData.closureStable CondensedCoefficientStageData.ambientFiniteShift
  CondensedCoefficientStageData.ambientClosureShift CondensedCoefficientStageData.finiteShift
  CondensedCoefficientStageData.closureShift

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The ShiftNormalization clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageShiftNormalization
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- Ambient shifts agree with the canonical exact, degreewise derived shifts. -/
  finiteShiftNormalization (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    @NatTrans.CommShift _ _ _ _ _ _ (finiteScalarLocalizationIso X ℓ h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ DerivedCategory.Q
        (derivedExtendScalarsSubfield X ℓ h) ℤ _ _ _ _ inferInstance
        (d.ambientFiniteShift E F h)) inferInstance
  /-- The same degreewise normalization at the algebraic closure. -/
  closureShiftNormalization (E : FiniteIntermediateField ℓ) :
    @NatTrans.CommShift _ _ _ _ _ _ (closureScalarLocalizationIso X ℓ E).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ DerivedCategory.Q
        (derivedExtendScalarsToPadicAlgCl X ℓ E) ℤ _ _ _ _ inferInstance
        (d.ambientClosureShift E)) inferInstance
  /-- Additivity of finite scalar extension on the full subcategories. -/
  finiteAdditive (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    (constructibleExtendScalars X ℓ h).Additive
  /-- Additivity of scalar extension to the vertex. -/
  closureAdditive (E : FiniteIntermediateField ℓ) : (constructibleToPadicAlgCl X ℓ E).Additive
  /-- The finite shift comparison is the restriction of the ambient one. -/
  finiteShiftRestriction (E F : FiniteIntermediateField ℓ) (h : E ≤ F) (n : ℤ)
      (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.map
        (((d.finiteShift E F h).commShiftIso n).hom.app K) ≫
      ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.commShiftIso n).hom.app
        ((constructibleExtendScalars X ℓ h).obj K) =
    (derivedExtendScalarsSubfield X ℓ h).map
        (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.commShiftIso n).hom.app K) ≫
      ((d.ambientFiniteShift E F h).commShiftIso n).hom.app K.obj
  /-- The vertex shift comparison is the restriction of the ambient one. -/
  closureShiftRestriction (E : FiniteIntermediateField ℓ) (n : ℤ)
      (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map
        (((d.closureShift E).commShiftIso n).hom.app K) ≫
      ((boundedConstructible (padicAlgClRingObj X ℓ)).ι.commShiftIso n).hom.app
        ((constructibleToPadicAlgCl X ℓ E).obj K) =
    (derivedExtendScalarsToPadicAlgCl X ℓ E).map
        (((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.commShiftIso n).hom.app K) ≫
      ((d.ambientClosureShift E).commShiftIso n).hom.app K.obj

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The TensorNormalization clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageTensorNormalization
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- On all complexes the unit is localization of ordinary tensor multiplication. -/
  unitNormalization (E : FiniteIntermediateField ℓ)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (d.ambientUnit E).hom.app (DerivedCategory.Q.obj K) =
      (finiteScalarLocalizationIso X ℓ (le_refl E)).hom.app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (Mod.extendScalarsIsoOfEq (d.coefficientId E) ≪≫
              Mod.extendScalarsId (R := padicSubfieldRingObj X ℓ E)) (ComplexShape.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app K)
  /-- Finite associators localize the ordinary tensor multiplication comparison. -/
  compNormalization (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (d.ambientComp E F G h k).hom.app (DerivedCategory.Q.obj K) ≫
        (finiteScalarLocalizationIso X ℓ (h.trans k)).hom.app K =
      (derivedExtendScalarsSubfield X ℓ k).map
          ((finiteScalarLocalizationIso X ℓ h).hom.app K) ≫
        (finiteScalarLocalizationIso X ℓ k).hom.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
                (padicSubfieldRingObjMap X ℓ k)).symm ≪≫
              Mod.extendScalarsIsoOfEq (d.coefficientComp E F G h k))
            (ComplexShape.up ℤ)).hom.app K)
  /-- The fixed ambient vertex comparison has the same tensor normalization. -/
  closureCompNormalization (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ) :
    (derivedExtendScalarsCompIso X ℓ h).hom.app (DerivedCategory.Q.obj K) ≫
        (closureScalarLocalizationIso X ℓ E).hom.app K =
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map
          ((finiteScalarLocalizationIso X ℓ h).hom.app K) ≫
        (closureScalarLocalizationIso X ℓ F).hom.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            ((Mod.extendScalarsComp (padicSubfieldRingObjMap X ℓ h)
                (padicSubfieldRingObjToPadicAlgCl X ℓ F)).symm ≪≫
              Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))
            (ComplexShape.up ℤ)).hom.app K)
  /-- Full-subcategory restriction of the ambient unit. -/
  unitRestriction (E : FiniteIntermediateField ℓ) (K : PadicSubfieldConstructible X ℓ E) :
    ((d.unit E).hom.app K).hom = (d.ambientUnit E).hom.app K.obj
  /-- Full-subcategory restriction of the ambient finite associator. -/
  compRestriction (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : PadicSubfieldConstructible X ℓ E) :
    ((d.comp E F G h k).hom.app K).hom = (d.ambientComp E F G h k).hom.app K.obj
  /-- Theta is the prescribed restriction, hence the one in `constructibleCocone`. -/
  thetaRestriction (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (derivedExtendScalarsCompIso X ℓ h).hom.app K.obj

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The Coherence clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageCoherence
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- Units commute with every integer shift. -/
  unitShift (E : FiniteIntermediateField ℓ) :
    @NatTrans.CommShift _ _ _ _ _ _ (d.unit E).hom ℤ _ _ _
      (d.finiteShift E E (le_refl E)) inferInstance
  /-- Finite associators commute with every integer shift. -/
  compShift (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G) :
    @NatTrans.CommShift _ _ _ _ _ _ (d.comp E F G h k).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (d.finiteShift E F h) (d.finiteShift F G k))
      (d.finiteShift E G (h.trans k))
  /-- Theta commutes with every integer shift. -/
  thetaShift (E F : FiniteIntermediateField ℓ) (h : E ≤ F) :
    @NatTrans.CommShift _ _ _ _ _ _ (constructibleToPadicAlgClCompIso X ℓ h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (d.finiteShift E F h) (d.closureShift F)) (d.closureShift E)
  /-- Left unit identity, evaluated at an arbitrary constructible complex. -/
  leftUnit (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    (d.comp E E F (le_refl E) h).hom.app K =
      (constructibleExtendScalars X ℓ h).map ((d.unit E).hom.app K)
  /-- Right unit identity. -/
  rightUnit (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : PadicSubfieldConstructible X ℓ E) :
    (d.comp E F F h (le_refl F)).hom.app K =
      (d.unit F).hom.app ((constructibleExtendScalars X ℓ h).obj K)
  /-- The corresponding unit identity for the vertex. -/
  thetaUnit (E : FiniteIntermediateField ℓ) (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgClCompIso X ℓ (le_refl E)).hom.app K =
      (constructibleToPadicAlgCl X ℓ E).map ((d.unit E).hom.app K)
  /-- The four-field cocycle; evaluating removes the canonical functor associator. -/
  associativity (E F G H : FiniteIntermediateField ℓ)
      (h : E ≤ F) (k : F ≤ G) (j : G ≤ H) (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleExtendScalars X ℓ j).map ((d.comp E F G h k).hom.app K) ≫
        (d.comp E G H (h.trans k) j).hom.app K =
      (d.comp F G H k j).hom.app ((constructibleExtendScalars X ℓ h).obj K) ≫
        (d.comp E F H h (k.trans j)).hom.app K
  /-- The same cocycle with algebraically closed final coefficient field. -/
  thetaAssociativity (E F G : FiniteIntermediateField ℓ) (h : E ≤ F) (k : F ≤ G)
      (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl X ℓ G).map ((d.comp E F G h k).hom.app K) ≫
        (constructibleToPadicAlgClCompIso X ℓ (h.trans k)).hom.app K =
      (constructibleToPadicAlgClCompIso X ℓ k).hom.app
          ((constructibleExtendScalars X ℓ h).obj K) ≫
        (constructibleToPadicAlgClCompIso X ℓ h).hom.app K

set_option maxHeartbeats 2000000 in
-- The internal module-object types require a larger elaboration budget.
/-- The Exactness clauses for the chosen scalar data.
The scoped elaboration budget accommodates the internal module-object types.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
structure CondensedCoefficientStageExactness
    [d : CondensedCoefficientStageData X ℓ] : Prop where
  /-- On Noetherian spaces the finite full subcategories are triangulated. -/
  finiteTriangulated (hX : TopologicalSpace.NoetherianSpace X) (E : FiniteIntermediateField ℓ) :
    (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated
  /-- On Noetherian spaces the vertex full subcategory is triangulated. -/
  closureTriangulated (hX : TopologicalSpace.NoetherianSpace X) :
    (boundedConstructible (padicAlgClRingObj X ℓ)).IsTriangulated
  /-- Exactness for the prescribed restricted shifts and induced distinguished triangles. -/
  finiteExact (hX : TopologicalSpace.NoetherianSpace X) (E F : FiniteIntermediateField ℓ)
      (h : E ≤ F) (T : Triangle (PadicSubfieldConstructible X ℓ E)) :
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.mapTriangle.obj T) ∈ distTriang _ →
      ((boundedConstructible (padicSubfieldRingObj X ℓ F)).ι.mapTriangle.obj
        ((@Functor.mapTriangle _ _ _ _ _ _ (constructibleExtendScalars X ℓ h)
          (d.finiteShift E F h)).obj T)) ∈ distTriang _
  /-- Exactness of the vertex functors for the ordinary restricted derived shift. -/
  closureExact (hX : TopologicalSpace.NoetherianSpace X) (E : FiniteIntermediateField ℓ)
      (T : Triangle (PadicSubfieldConstructible X ℓ E)) :
    ((boundedConstructible (padicSubfieldRingObj X ℓ E)).ι.mapTriangle.obj T) ∈ distTriang _ →
      ((boundedConstructible (padicAlgClRingObj X ℓ)).ι.mapTriangle.obj
        ((@Functor.mapTriangle _ _ _ _ _ _ (constructibleToPadicAlgCl X ℓ E)
          (d.closureShift E)).obj T)) ∈ distTriang _

/-- Exactly the ambient normalizations, restricted comparisons, coherence, and
conditional exactness required of the chosen condensed scalar data.
Source: latest blueprint `sk-thm-sfb-qlbar-two-colimit`, its scalar-extension
paragraph and composition proofs, and `def-sfb-constructible-cocone`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
def CondensedCoefficientStageNormalized (d : CondensedCoefficientStageData X ℓ) : Prop :=
  @CondensedCoefficientStageShiftNormalization X ℓ _ d ∧
    @CondensedCoefficientStageTensorNormalization X ℓ _ d ∧
    @CondensedCoefficientStageCoherence X ℓ _ d ∧
    @CondensedCoefficientStageExactness X ℓ _ d

end AlgebraicGeometry.ProEtale
