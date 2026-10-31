/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjectionSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.RestrictedTowerResolutionAcyclicity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Resolution-normalized comparison for the quotient sequence projection

Source: Stacks 0D6E, 070I, 070K and 070Y; the coefficient-comparison paragraph of
`fix-prop-coherence.proof.md`
(blueprint: lem-pur-sequence-kinjective-comparison-shifts).

The constant-ring factorization has exact direct image `coefficientSequenceRestriction`
and second direct image `lim`. Thus the direct image of the supplied ringed projection
is their composite `push`. All module categories below are the recorded actual coefficient
categories, retaining the independent scheme and coefficient universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.sequenceSmall WeilConjectures.SemilinearSections.sliceSmall
attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence SheafOfModules.monoidalCategory
  HasDerivedCategory.standard
attribute [local instance high] HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceRestriction
  SheafOfModules.strictRingSystemAbelian

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.ringedToposCommRingForgetCompose
  CategoryTheory.ringedToposRingForgetCompose CategoryTheory.ringedToposAbelianForgetCompose

namespace WeilConjectures.SequenceKInjectiveComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{t})

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def derivedUnit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
    DerivedCategory.Qh).inv ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _) F.rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    F.rightDerivedFunctor).hom

private theorem derivedUnit_app
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (derivedUnit F).app K = coefficientRightDerivedComparison F K := by
  dsimp only [derivedUnit, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app]
  change _ = coefficientRightDerivedComparison F K
  simp only [Category.id_comp]
  change (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
      DerivedCategory.Qh.map (𝟙 _) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
          F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K) = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl


private theorem derivedUnit_commShift
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] : NatTrans.CommShift (derivedUnit F) ℤ := by
  have := CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift (DerivedCategory.quotientCompQhIso B).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (F.mapHomotopyCategoryFactors (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  dsimp only [derivedUnit]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom]
  infer_instance

private def compositeUnit
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.rightDerivedFunctor) :=
  Functor.whiskerRight
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv
      DerivedCategory.Q ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (derivedUnit G) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight F.mapDerivedCategoryFactors.inv G.rightDerivedFunctor ≫
  (Functor.associator _ _ _).hom

private theorem compositeUnit_app
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (N : CochainComplex A ℤ) :
    (compositeUnit F G).app N =
      coefficientRightDerivedComparison G ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app N) := by
  dsimp only [compositeUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, derivedUnit_app]
  change DerivedCategory.Q.map (𝟙 _) ≫ _ = _
  rw [DerivedCategory.Q.map_id, Category.id_comp]

private theorem compositeUnit_commShift
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift (compositeUnit F G) ℤ := by
  have := derivedUnit_commShift G
  have : NatTrans.CommShift F.mapDerivedCategoryFactors.inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  dsimp only [compositeUnit]
  infer_instance

private def unitQNat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K := F.rightDerivedFunctorUnitQ K
  naturality _ _ f := Functor.rightDerivedFunctorUnitQ_naturality F f

private theorem unitQNat_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift (unitQNat F) ℤ := by
  have he : unitQNat F = derivedUnit F := by
    ext K
    exact (derivedUnit_app F K).symm
  rw [he]
  exact derivedUnit_commShift F

private theorem model_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) [J.IsKInjective] (r : ℤ) :
    (F.rightDerivedFunctorObjQIso (J⟦r⟧)).hom ≫
        DerivedCategory.Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app J) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) =
      F.rightDerivedFunctor.map ((DerivedCategory.Q.commShiftIso r).hom.app J) ≫
        (F.rightDerivedFunctor.commShiftIso r).hom.app (DerivedCategory.Q.obj J) ≫
          (F.rightDerivedFunctorObjQIso J).hom⟦r⟧' := by
  have : NatTrans.CommShift (unitQNat F) ℤ := unitQNat_shift F
  have h := NatTrans.shift_app_comm (unitQNat F) r J
  simp only [Functor.commShiftIso_comp_hom_app, unitQNat,
    Functor.rightDerivedFunctorUnitQ_eq] at h
  apply (cancel_epi (F.rightDerivedFunctorObjQIso (J⟦r⟧)).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have hc : (F.rightDerivedFunctorObjQIso J).inv⟦r⟧' ≫
      (F.rightDerivedFunctorObjQIso J).hom⟦r⟧' = 𝟙 _ :=
    ((shiftFunctor (DerivedCategory D) r).mapIso (F.rightDerivedFunctorObjQIso J)).inv_hom_id
  have hx := congrArg (fun f ↦ f ≫ (F.rightDerivedFunctorObjQIso J).hom⟦r⟧') h
  simp only [Category.assoc, hc] at hx
  erw [Category.comp_id] at hx
  exact hx

section GenericComparison
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Localization, followed by the supplied replacement and its K-injective limit model.
Source: Stacks 070K and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def comparisonIso (N : CochainComplex A ℤ)
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj J) :=
  G.rightDerivedFunctor.mapIso (F.mapDerivedCategoryFactors.app N) ≪≫
    G.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map v)) ≪≫
      G.rightDerivedFunctorObjQIso J

/-- Supplied-replacement shift equation for exact restriction followed by an additive functor.
Source: Stacks 070K and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ReplacementShiftsFor : Prop :=
  ∀ (N : CochainComplex A ℤ) (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (comparisonIso F G (N⟦r⟧) (J⟦r⟧)
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧')).hom ≫
      DerivedCategory.Q.map (((G.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app J) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj J) =
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).map
        ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((F.mapDerivedCategory ⋙ G.rightDerivedFunctor).commShiftIso r).hom.app
        (DerivedCategory.Q.obj N) ≫ (comparisonIso F G N J v).hom⟦r⟧'

private theorem comparisonIso_shifts : ReplacementShiftsFor F G := by
  intro N J _ v _ r
  have hR := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom r N
  have hm := model_shift G J r
  dsimp only [comparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [hm]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc] at hR ⊢
  rw [← G.rightDerivedFunctor.map_comp_assoc,
    ← G.rightDerivedFunctor.map_comp_assoc,
    ← G.rightDerivedFunctor.map_comp_assoc]
  have hs : F.mapDerivedCategoryFactors.hom.app (N⟦r⟧) ≫
      DerivedCategory.Q.map (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N) ≫
      DerivedCategory.Q.map (v⟦r⟧') ≫ (DerivedCategory.Q.commShiftIso r).hom.app J =
    F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      (F.mapDerivedCategory.commShiftIso r).hom.app (DerivedCategory.Q.obj N) ≫
      F.mapDerivedCategoryFactors.hom.app N⟦r⟧' ≫ (DerivedCategory.Q.map v)⟦r⟧' := by
    rw [DerivedCategory.Q.commShiftIso_hom_naturality]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (DerivedCategory.Q.map v)⟦r⟧') hR.symm
  simp only [Category.assoc]
  rw [hs]
  simp only [Functor.map_comp, Functor.commShiftIso_hom_naturality_assoc, Category.assoc]

private theorem comparisonIso_naturality
    {N N' : CochainComplex A ℤ}
    (J J' : CochainComplex B ℤ) [J.IsKInjective] [J'.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (v' : (F.mapHomologicalComplex (.up ℤ)).obj N' ⟶ J') [QuasiIso v']
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') (s : J ⟶ J')
    (hs : DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
        F.mapDerivedCategoryFactors.hom.app N' ≫ DerivedCategory.Q.map v') :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).map f ≫
      (comparisonIso F G N' J' v').hom =
    (comparisonIso F G N J v).hom ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s) := by
  have hn := Functor.rightDerivedFunctorUnitQ_naturality G s
  rw [Functor.rightDerivedFunctorUnitQ_eq, Functor.rightDerivedFunctorUnitQ_eq] at hn
  have hm : G.rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
      (G.rightDerivedFunctorObjQIso J').hom =
    (G.rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s) := by
    apply (cancel_epi (G.rightDerivedFunctorObjQIso J).inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      using congrArg (fun f ↦ f ≫ (G.rightDerivedFunctorObjQIso J').hom) hn.symm
  dsimp only [comparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    asIso_hom, Functor.comp_map]
  simp only [Category.assoc]
  rw [← hm]
  have he : F.mapDerivedCategory.map f ≫ F.mapDerivedCategoryFactors.hom.app N' ≫
      DerivedCategory.Q.map v' =
    F.mapDerivedCategoryFactors.hom.app N ≫ DerivedCategory.Q.map v ≫
      DerivedCategory.Q.map s := by
    rw [hs]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [← G.rightDerivedFunctor.map_comp_assoc]
  rw [he]

private theorem compositeUnit_normalization
    (I : CochainComplex A ℤ) (J : CochainComplex B ℤ) [J.IsKInjective]
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    (compositeUnit F G).app I ≫ (comparisonIso F G I J j).hom =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j) := by
  have hn := Functor.rightDerivedFunctorUnitQ_naturality G j
  rw [Functor.rightDerivedFunctorUnitQ_eq] at hn
  rw [compositeUnit_app]
  dsimp only [comparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom]
  simp only [Category.assoc, ← G.rightDerivedFunctor.map_comp_assoc,
    Iso.inv_hom_id_app_assoc]
  change coefficientRightDerivedComparison G _ ≫
      G.rightDerivedFunctor.map (DerivedCategory.Q.map j) ≫ _ = _
  change G.rightDerivedFunctorUnitQ _ ≫ _ = _
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]



private theorem comparisonIso_arbitrary
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j))
    (N I : CochainComplex A ℤ) [I.IsKInjective] (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso β]
    (hh : Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v)) :
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map β) ∧
      (compositeUnit F G).app I ≫
        inv ((F.mapDerivedCategory ⋙ G.rightDerivedFunctor).map (DerivedCategory.Q.map i)) ≫
          (comparisonIso F G N J v).hom =
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map β) := by
  refine ⟨hacyc I J β, ?_⟩
  have hd := DerivedCategory.Q_map_eq_of_homotopy B hh.some
  simp only [Functor.map_comp] at hd
  have ht : F.mapDerivedCategoryFactors.inv.app N ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map i) ≫
        F.mapDerivedCategoryFactors.hom.app I =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i) := by
    have hn := F.mapDerivedCategoryFactors.hom.naturality i
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [Iso.inv_hom_id_app_assoc]
  have hn := comparisonIso_naturality F G J J v β (DerivedCategory.Q.map i) (𝟙 J) (by
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, ← ht] at hd ⊢
    simpa only [Category.assoc] using hd.symm)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  rw [← hn]
  simp only [IsIso.inv_hom_id_assoc]
  exact compositeUnit_normalization F G I J β


private theorem compositeUnit_isIso
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j))
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso ((compositeUnit F G).app I) := by
  obtain ⟨J, hJ, j, _, hj⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) := hacyc I J j
  have : IsIso ((compositeUnit F G).app I ≫ (comparisonIso F G I J j).hom) := by
    rw [compositeUnit_normalization]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (comparisonIso F G I J j).hom


end GenericComparison

attribute [local irreducible] ReplacementShiftsFor comparisonIso
/-- Representative shift identities for two additive termwise functors.
Source: Stacks 070H, 070I, 070K
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def RepresentativeShiftsFor
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
    (∀ (J J' : CochainComplex B ℤ)
    (j : J ⟶ J') (r i : ℤ),
      ((G.mapHomologicalComplex (.up ℤ)).map (j⟦r⟧')).f i =
        ((G.mapHomologicalComplex (.up ℤ)).map j).f (i + r)) ∧
  (∀ (J : CochainComplex B ℤ) (r i j : ℤ),
    ((G.mapHomologicalComplex (.up ℤ)).obj (J⟦r⟧)).d i j =
      r.negOnePow • ((G.mapHomologicalComplex (.up ℤ)).obj J).d (i + r) (j + r)) ∧
  (∀ (N : CochainComplex A ℤ)
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (J⟦r⟧).IsKInjective ∧
      QuasiIso (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧')) ∧
  ∀ (N I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J),
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v) → ∀ r : ℤ,
    (I⟦r⟧).IsKInjective ∧ QuasiIso (i⟦r⟧') ∧
      Nonempty (Homotopy
        ((F.mapHomologicalComplex (.up ℤ)).map (i⟦r⟧') ≫
          ((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app I ≫ β⟦r⟧')
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N ≫ v⟦r⟧'))

private theorem representativeShifts_generic
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    RepresentativeShiftsFor F G := by
  unfold RepresentativeShiftsFor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro J J' j r i
    rfl
  · intro J r i j
    exact Functor.map_units_smul
      G
      (r.negOnePow) (J.d (i + r) (j + r))
  · intro N J _ v _ r
    exact ⟨inferInstance, inferInstance⟩
  · intro N I _ i _ J _ v _ β h r
    refine ⟨inferInstance, inferInstance, ?_⟩
    obtain ⟨h⟩ := h
    have hs := (h.shift r).compLeft (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app N)
    refine ⟨(Homotopy.ofEq ?_).trans hs⟩
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ β⟦r⟧')
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.naturality i)


section GenericProperties
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Transport a localized morphism through exact restriction.
Source: Stacks 05RU
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictedMapFor {N N' : CochainComplex A ℤ}
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj N) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj N') :=
  F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
    F.mapDerivedCategoryFactors.hom.app N'

/-- Generic Normalization predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def NormalizationFor
    (RP : DerivedCategory A ⥤ DerivedCategory (C))
    (η : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)) : Prop :=
  (∀ N : CochainComplex (A) ℤ,
    η.app N ≫ κ.hom.app (DerivedCategory.Q.obj N) =
      coefficientRightDerivedComparison G ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        (G.rightDerivedFunctor).map ((F.mapDerivedCategoryFactors).inv.app N)) ∧
  ∀ (I : CochainComplex (A) ℤ) [I.IsKInjective]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
    QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) ∧
      η.app I ≫ κ.hom.app (DerivedCategory.Q.obj I) ≫
        (comparisonIso F G I J j).hom =
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map j)

/-- Generic ArbitraryReplacement predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ArbitraryReplacementFor
    (RP : DerivedCategory A ⥤ DerivedCategory (C))
    (η : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)) : Prop :=
  ∀ (N I : CochainComplex (A) ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex B ℤ) [J.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v],
    ∃ b : (HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj J,
      (∀ b' : (HomotopyCategory.quotient _ (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
          (HomotopyCategory.quotient _ (.up ℤ)).obj J,
        (HomotopyCategory.quotient _ (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map i) ≫ b' =
          (HomotopyCategory.quotient _ (.up ℤ)).map v ↔ b' = b) ∧
      ∀ β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J,
        (HomotopyCategory.quotient _ (.up ℤ)).map β = b →
        QuasiIso β ∧ QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map β) ∧
          η.app I ≫ inv (RP.map (DerivedCategory.Q.map i)) ≫
            κ.hom.app (DerivedCategory.Q.obj N) ≫ (comparisonIso F G N J v).hom =
              DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map β)

/-- Generic DerivedNaturality predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def DerivedNaturalityFor : Prop :=
  ∀ (N N' I I' : CochainComplex (A) ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] (i' : N' ⟶ I') [QuasiIso i']
    (J J' : CochainComplex B ℤ)
    [J.IsKInjective] [J'.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J) [QuasiIso v]
    (v' : (F.mapHomologicalComplex (.up ℤ)).obj N' ⟶ J') [QuasiIso v']
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (t : I ⟶ I') (s : J ⟶ J')
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (β' : (F.mapHomologicalComplex (.up ℤ)).obj I' ⟶ J'),
    DerivedCategory.Q.map i ≫ DerivedCategory.Q.map t = f ≫ DerivedCategory.Q.map i' →
    DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      restrictedMapFor F f ≫ DerivedCategory.Q.map v' →
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v) →
    Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i' ≫ β') v') →
    Nonempty (Homotopy (β ≫ s) ((F.mapHomologicalComplex (.up ℤ)).map t ≫ β')) ∧
      ((F.mapDerivedCategory ⋙ G.rightDerivedFunctor)).map f ≫ (comparisonIso F G N' J' v').hom =
        (comparisonIso F G N J v).hom ≫
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s)

/-- Generic ResolutionCocycle predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ResolutionCocycleFor : Prop :=
  ∀ (N : CochainComplex (A) ℤ)
    (J₀ J₁ J₂ : CochainComplex B ℤ)
    [J₀.IsKInjective] [J₁.IsKInjective] [J₂.IsKInjective]
    (v₀ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₀) [QuasiIso v₀]
    (v₁ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₁) [QuasiIso v₁]
    (v₂ : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J₂) [QuasiIso v₂]
    (s₀₁ : J₀ ⟶ J₁) (s₁₂ : J₁ ⟶ J₂) (s₀₂ : J₀ ⟶ J₂) (s₀₀ : J₀ ⟶ J₀),
    Nonempty (Homotopy (v₀ ≫ s₀₁) v₁) →
    Nonempty (Homotopy (v₁ ≫ s₁₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₀) v₀) →
    Nonempty (Homotopy (s₀₁ ≫ s₁₂) s₀₂) ∧ Nonempty (Homotopy s₀₀ (𝟙 J₀)) ∧
      (comparisonIso F G N J₀ v₀).hom ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₁) =
          (comparisonIso F G N J₁ v₁).hom ∧
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₁) ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₁₂) =
          DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₂) ∧
      DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s₀₀) = 𝟙 _

/-- Generic SystemResolutionCocycle predicate for an exact additive first factor.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def SystemResolutionCocycleFor : Prop :=
  ∀ (N I₀ I₁ I₂ : CochainComplex (A) ℤ)
    [I₀.IsKInjective] [I₁.IsKInjective] [I₂.IsKInjective]
    (i₀ : N ⟶ I₀) [QuasiIso i₀] (i₁ : N ⟶ I₁) [QuasiIso i₁]
    (i₂ : N ⟶ I₂) [QuasiIso i₂]
    (t₀₁ : I₀ ⟶ I₁) (t₁₂ : I₁ ⟶ I₂) (t₀₂ : I₀ ⟶ I₂) (t₀₀ : I₀ ⟶ I₀),
    Nonempty (Homotopy (i₀ ≫ t₀₁) i₁) → Nonempty (Homotopy (i₁ ≫ t₁₂) i₂) →
    Nonempty (Homotopy (i₀ ≫ t₀₂) i₂) → Nonempty (Homotopy (i₀ ≫ t₀₀) i₀) →
    Nonempty (Homotopy (t₀₁ ≫ t₁₂) t₀₂) ∧ Nonempty (Homotopy t₀₀ (𝟙 I₀)) ∧
      DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₁) ≫
        DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₁₂) =
          DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₂) ∧
      DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map t₀₀) = 𝟙 _

private theorem homotopy_of_derived_eq
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K J : CochainComplex A ℤ} [J.IsKInjective] (f g : K ⟶ J)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app J)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

private theorem derived_eq_of_homotopy
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {K J : CochainComplex A ℤ} {f g : K ⟶ J} (h : Nonempty (Homotopy f g)) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  DerivedCategory.Q_map_eq_of_homotopy A h.some

private theorem map_derived_eq_of_homotopy
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    {K J : CochainComplex A ℤ} {f g : K ⟶ J} (h : Nonempty (Homotopy f g)) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) :=
  derived_eq_of_homotopy (h.map fun h ↦ F.mapHomotopy h)

private theorem cancellation_homotopies
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {N I₀ I₁ I₂ : CochainComplex A ℤ} [I₀.IsKInjective] [I₂.IsKInjective]
    (i₀ : N ⟶ I₀) [QuasiIso i₀] (i₁ : N ⟶ I₁) (i₂ : N ⟶ I₂)
    (t₀₁ : I₀ ⟶ I₁) (t₁₂ : I₁ ⟶ I₂) (t₀₂ : I₀ ⟶ I₂) (t₀₀ : I₀ ⟶ I₀)
    (h₀₁ : Nonempty (Homotopy (i₀ ≫ t₀₁) i₁))
    (h₁₂ : Nonempty (Homotopy (i₁ ≫ t₁₂) i₂))
    (h₀₂ : Nonempty (Homotopy (i₀ ≫ t₀₂) i₂))
    (h₀₀ : Nonempty (Homotopy (i₀ ≫ t₀₀) i₀)) :
    Nonempty (Homotopy (t₀₁ ≫ t₁₂) t₀₂) ∧ Nonempty (Homotopy t₀₀ (𝟙 I₀)) := by
  constructor
  · apply homotopy_of_derived_eq
    apply (cancel_epi (DerivedCategory.Q.map i₀)).mp
    have h₁ := derived_eq_of_homotopy h₀₁
    have h₂ := derived_eq_of_homotopy h₁₂
    have h₃ := derived_eq_of_homotopy h₀₂
    simp only [Functor.map_comp] at h₁ h₂ h₃ ⊢
    rw [← Category.assoc, h₁, h₂, h₃]
  · apply homotopy_of_derived_eq
    apply (cancel_epi (DerivedCategory.Q.map i₀)).mp
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    simpa only [Functor.map_comp] using derived_eq_of_homotopy h₀₀

private theorem comparison_class
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {N I J : CochainComplex A ℤ} [J.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] (v : N ⟶ J) :
    ∃ b : (HomotopyCategory.quotient A (.up ℤ)).obj I ⟶
        (HomotopyCategory.quotient A (.up ℤ)).obj J,
      ∀ b', (HomotopyCategory.quotient A (.up ℤ)).map i ≫ b' =
        (HomotopyCategory.quotient A (.up ℤ)).map v ↔ b' = b := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : IsIso (DerivedCategory.Qh.map (q.map i)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) i).mpr inferInstance
  have hi : Function.Injective (fun b : q.obj I ⟶ q.obj J ↦ q.map i ≫ b) := by
    intro b c h
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
    apply (cancel_epi (DerivedCategory.Qh.map (q.map i))).mp
    simpa only [← Functor.map_comp] using congrArg DerivedCategory.Qh.map h
  obtain ⟨b, hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) J).surjective
    (inv (DerivedCategory.Qh.map (q.map i)) ≫ DerivedCategory.Qh.map (q.map v))
  have hb' : q.map i ≫ b = q.map v := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
    simp only [Functor.map_comp, hb, IsIso.hom_inv_id_assoc]
  exact ⟨b, fun b' ↦ ⟨fun h ↦ hi (h.trans hb'.symm), fun h ↦ h ▸ hb'⟩⟩

private theorem resolution_naturality
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {N N' I I' : CochainComplex A ℤ} [I.IsKInjective] [I'.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] (i' : N' ⟶ I') [QuasiIso i']
    {J J' : CochainComplex B ℤ} [J'.IsKInjective]
    (v : (F.mapHomologicalComplex (.up ℤ)).obj N ⟶ J)
    (v' : (F.mapHomologicalComplex (.up ℤ)).obj N' ⟶ J')
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (t : I ⟶ I') (s : J ⟶ J')
    (β : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    (β' : (F.mapHomologicalComplex (.up ℤ)).obj I' ⟶ J')
    (ht : DerivedCategory.Q.map i ≫ DerivedCategory.Q.map t =
      f ≫ DerivedCategory.Q.map i')
    (hs : DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
        F.mapDerivedCategoryFactors.hom.app N' ≫ DerivedCategory.Q.map v')
    (hb : Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v))
    (hb' : Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i' ≫ β') v')) :
    Nonempty (Homotopy (β ≫ s) ((F.mapHomologicalComplex (.up ℤ)).map t ≫ β')) := by
  have hb₁ := derived_eq_of_homotopy hb
  have hb₂ := derived_eq_of_homotopy hb'
  simp only [Functor.map_comp] at hb₁ hb₂
  have hn (K L : CochainComplex A ℤ) (a : K ⟶ L) :
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) =
        F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map
          (DerivedCategory.Q.map a) ≫ F.mapDerivedCategoryFactors.hom.app L := by
    have h := F.mapDerivedCategoryFactors.hom.naturality a
    dsimp only [Functor.comp_map] at h
    rw [h]
    simp only [Iso.inv_hom_id_app_assoc]
  have ht' : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map t) =
      (F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
        F.mapDerivedCategoryFactors.hom.app N') ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i') := by
    simp only [hn, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← F.mapDerivedCategory.map_comp_assoc, ht, F.mapDerivedCategory.map_comp]
    simp only [Category.assoc]
  apply homotopy_of_derived_eq
  apply (cancel_epi (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i))).mp
  simp only [Functor.map_comp]
  calc
    _ = DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s := by
      rw [← Category.assoc, hb₁]
    _ = (F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
        F.mapDerivedCategoryFactors.hom.app N') ≫ DerivedCategory.Q.map v' := by
      simpa only [Category.assoc] using hs
    _ = _ := by rw [← hb₂, ← Category.assoc, ← ht', Category.assoc]


private theorem normalizationFor_app
    {RP : DerivedCategory A ⥤ DerivedCategory C}
    {η : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP}
    {κ : RP ≅ F.mapDerivedCategory ⋙ G.rightDerivedFunctor}
    (hn : NormalizationFor F G RP η κ) (N : CochainComplex A ℤ) :
    η.app N ≫ κ.hom.app (DerivedCategory.Q.obj N) =
      coefficientRightDerivedComparison G ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app N) := hn.1 N

private theorem normalization_generic
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    NormalizationFor F G (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)
      (compositeUnit F G) (Iso.refl _) := by
  constructor
  · intro N
    change (compositeUnit F G).app N ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact compositeUnit_app F G N
  · intro I _ J _ j _
    exact ⟨hacyc I J j, by
      change (compositeUnit F G).app I ≫ 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact compositeUnit_normalization F G I J j⟩

private theorem arbitraryReplacement_generic
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    ArbitraryReplacementFor F G (F.mapDerivedCategory ⋙ G.rightDerivedFunctor)
      (compositeUnit F G) (Iso.refl _) := by
  intro N I _ i _ J _ v _
  obtain ⟨b, hb⟩ := comparison_class ((F.mapHomologicalComplex (.up ℤ)).map i) v
  refine ⟨b, hb, ?_⟩
  intro β hβ
  have he : Nonempty (Homotopy ((F.mapHomologicalComplex (.up ℤ)).map i ≫ β) v) := by
    apply Nonempty.intro
    apply HomotopyCategory.homotopyOfEq
    simpa only [Functor.map_comp, hβ] using (hb b).mpr rfl
  have hq := derived_eq_of_homotopy he
  have hβq : QuasiIso β := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ β).mp
    have hv : IsIso (DerivedCategory.Q.map v) := inferInstance
    rw [← hq, Functor.map_comp] at hv
    exact IsIso.of_isIso_comp_left
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i)) (DerivedCategory.Q.map β)
  obtain ⟨hlim, heq⟩ := comparisonIso_arbitrary F G hacyc N I i J v β he
  refine ⟨hβq, hlim, ?_⟩
  simpa only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] using heq

private theorem derivedNaturality_generic : DerivedNaturalityFor F G := by
  intro N N' I I' _ _ i _ i' _ J J' _ _ v _ v' _ f t s β β' ht hs hb hb'
  dsimp only [restrictedMapFor] at hs
  have hs' := (by simpa only [Category.assoc] using hs :
    DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      F.mapDerivedCategoryFactors.inv.app N ≫ F.mapDerivedCategory.map f ≫
        F.mapDerivedCategoryFactors.hom.app N' ≫ DerivedCategory.Q.map v')
  exact ⟨resolution_naturality F i i' v v' f t s β β' ht hs' hb hb',
    comparisonIso_naturality F G J J' v v' f s hs'⟩

private theorem resolutionCocycle_generic : ResolutionCocycleFor F G := by
  intro N J₀ J₁ J₂ _ _ _ v₀ _ v₁ _ v₂ _ s₀₁ s₁₂ s₀₂ s₀₀ h₀₁ h₁₂ h₀₂ h₀₀
  obtain ⟨hc, hi⟩ := cancellation_homotopies v₀ v₁ v₂ s₀₁ s₁₂ s₀₂ s₀₀
    h₀₁ h₁₂ h₀₂ h₀₀
  refine ⟨hc, hi, ?_, ?_, ?_⟩
  · have hs := derived_eq_of_homotopy h₀₁
    simp only [Functor.map_comp] at hs
    have hn := comparisonIso_naturality F G J₀ J₁ v₀ v₁ (𝟙 _) s₀₁ (by
      rw [F.mapDerivedCategory.map_id]
      change DerivedCategory.Q.map v₀ ≫ DerivedCategory.Q.map s₀₁ =
        F.mapDerivedCategoryFactors.inv.app N ≫
          (𝟙 _ ≫ (F.mapDerivedCategoryFactors.hom.app N ≫ DerivedCategory.Q.map v₁))
      erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
      exact hs)
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hn.symm
  · simpa only [Functor.map_comp] using map_derived_eq_of_homotopy G hc
  · simpa only [CategoryTheory.Functor.map_id] using map_derived_eq_of_homotopy G hi

omit [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem systemResolutionCocycle_generic : SystemResolutionCocycleFor F G := by
  intro N I₀ I₁ I₂ _ _ _ i₀ _ i₁ _ i₂ _ t₀₁ t₁₂ t₀₂ t₀₀ h₀₁ h₁₂ h₀₂ h₀₀
  obtain ⟨hc, hi⟩ := cancellation_homotopies i₀ i₁ i₂ t₀₁ t₁₂ t₀₂ t₀₀
    h₀₁ h₁₂ h₀₂ h₀₀
  refine ⟨hc, hi, ?_, ?_⟩
  · simpa only [Functor.map_comp] using map_derived_eq_of_homotopy (F ⋙ G) hc
  · simpa only [CategoryTheory.Functor.map_id] using map_derived_eq_of_homotopy (F ⋙ G) hi


variable [Abelian.HasKInjectiveResolutions A]

private theorem compositeUnit_derived
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (compositeUnit F G) (HomologicalComplex.quasiIso A (.up ℤ)) := by
  apply (CategoryTheory.derives (F ⋙ G)).isRightDerivedFunctor_of_isIso (compositeUnit F G)
  intro I
  have : I.obj.IsKInjective := I.property
  exact compositeUnit_isIso F G hacyc I.obj

private theorem genericComparison
    (hacyc : ∀ (I : CochainComplex A ℤ) [I.IsKInjective]
      (J : CochainComplex B ℤ) [J.IsKInjective]
      (j : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso j],
      QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j)) :
    ∃ (RP : DerivedCategory A ⥤ DerivedCategory C)
      (η : (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RP) (sRP : RP.CommShift ℤ),
      RP.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso (η.app I)) ∧
      (fun [_s : RP.CommShift ℤ] ↦ NatTrans.CommShift η ℤ ∧
        ∃! κ : RP ≅ F.mapDerivedCategory ⋙ G.rightDerivedFunctor,
          NormalizationFor F G RP η κ ∧ ArbitraryReplacementFor F G RP η κ ∧
          NatTrans.CommShift κ.hom ℤ ∧ DerivedNaturalityFor F G ∧
          ResolutionCocycleFor F G ∧ SystemResolutionCocycleFor F G ∧
          RepresentativeShiftsFor F G ∧ ReplacementShiftsFor F G) (_s := sRP) := by
  have hd := compositeUnit_derived F G hacyc
  refine ⟨F.mapDerivedCategory ⋙ G.rightDerivedFunctor, compositeUnit F G, inferInstance,
    hd, compositeUnit_isIso F G hacyc, compositeUnit_commShift F G, Iso.refl _, ?_, ?_⟩
  · exact ⟨normalization_generic F G hacyc, arbitraryReplacement_generic F G hacyc,
      (by change NatTrans.CommShift (𝟙 _) ℤ; infer_instance),
      derivedNaturality_generic F G, resolutionCocycle_generic F G,
      systemResolutionCocycle_generic F G, representativeShifts_generic F G,
      comparisonIso_shifts F G⟩
  · intro κ hκ
    apply Iso.ext
    let := hd
    apply Functor.rightDerived_ext _ (compositeUnit F G)
      (HomologicalComplex.quasiIso A (.up ℤ)) _ _ _
    ext N
    change (compositeUnit F G).app N ≫ κ.hom.app _ =
      (compositeUnit F G).app N ≫ 𝟙 _
    rw [Category.comp_id]
    exact (normalizationFor_app F G hκ.1 N).trans (compositeUnit_app F G N).symm

end GenericProperties

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual termwise scalar restriction on cochain complexes.
Source: Stacks 0941 (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrict : CochainComplex (coefficientSequenceModules l E W) ℤ ⥤
    CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- Termwise inverse limit of the recorded constant-coefficient towers.
Source: Stacks 0941 (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def limitComplex : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ ⥤
    CochainComplex (scalarReductionSource l E W) ℤ :=
  Functor.mapHomologicalComplex
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) (.up ℤ)

/-- The ordinary module direct image of the quotient projection, factored through `cA`.
Its first factor changes only scalars along the completion projections; the second
forms the actual limit cone. This fixes `a_* = U`, `g_* = lim`, and `p_* = g_* a_*`.
Source: Stacks 0D6E, 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def push : coefficientSequenceModules l E W ⥤ scalarReductionSource l E W :=
  coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- The factored direct image is additive.
Source: Stacks 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance push_additive : (push l E W).Additive :=
  inferInstanceAs ((coefficientSequenceRestriction l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).Additive)

/-- Scalar restriction has its canonical termwise shift comparison.
Source: Stacks 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance restrict_shift : (restrict l E W).CommShift ℤ :=
  inferInstanceAs
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).CommShift ℤ)

/-- Termwise inverse limit has its canonical shift comparison.
Source: Stacks 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance limitComplex_shift : (limitComplex l E W).CommShift ℤ :=
  inferInstanceAs (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).CommShift ℤ)

/-- The fixed exact-localization comparison for restriction, without choosing resolutions.
Source: Stacks 05RU, 0941
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictionFactors :
    DerivedCategory.Q ⋙ coefficientSequenceDerivedRestriction l E W ≅
      restrict l E W ⋙ DerivedCategory.Q :=
  (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors

/-- The canonical comparison to total inverse limit on every tower complex.
Source: Stacks 070K, 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def limitUnit (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    DerivedCategory.Q.obj ((limitComplex l E W).obj J) ⟶
      (coefficientConstantTowerLimit l E W).obj (DerivedCategory.Q.obj J) :=
  coefficientRightDerivedComparison
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J

attribute [local irreducible] restrictionFactors limitUnit

/-- The canonical isomorphism for an arbitrary supplied simultaneous replacement.
It is exactly localization for `U`, followed by `Rlim([v])`, followed by the
K-injective model comparison. Its construction makes no choice of a resolution of `N`.
Source: Stacks 070K, 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def replacementIso (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v] :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj ((limitComplex l E W).obj J) :=
  (coefficientConstantTowerLimit l E W).mapIso ((restrictionFactors l E W).app N) ≪≫
    (coefficientConstantTowerLimit l E W).mapIso (asIso (DerivedCategory.Q.map v)) ≪≫
      Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) J

/-- Transport an arbitrary derived morphism through the exact localization comparison.
Source: Stacks 05RU (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def restrictedMap {N N' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Q.obj ((restrict l E W).obj N) ⟶
      DerivedCategory.Q.obj ((restrict l E W).obj N') :=
  (restrictionFactors l E W).inv.app N ≫
    (coefficientSequenceDerivedRestriction l E W).map f ≫
      (restrictionFactors l E W).hom.app N'

attribute [local irreducible] replacementIso restrictedMap

/-- The composite total limit has the standard coherent cochain shifts.
Source: Stacks 070K (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
instance totalLimitCommShift : (coefficientSequenceLimit l E W).CommShift ℤ :=
  inferInstanceAs (((coefficientSequenceRestriction l E W).mapDerivedCategory ⋙
    Functor.rightDerivedFunctor
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)).CommShift ℤ)

attribute [local irreducible] NormalizationFor ArbitraryReplacementFor
  DerivedNaturalityFor ResolutionCocycleFor SystemResolutionCocycleFor

/-- The normalization of the natural comparison at every K-injective system.
Source: Stacks 0D6E and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def Normalization
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  NormalizationFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) RP η κ

/-- Every supplied pair of resolutions has a unique comparison homotopy class `b` with
`b ∘ Ui ≃ v` (uniqueness among all classes satisfying this equation alone).
Every chain representative is a quasi-isomorphism, and its ordinary limit represents
the normalized composite, using the model of `RP[N]` supplied by `i`.
Source: Stacks 070I, 070K, 070Y and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ArbitraryReplacement
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  ArbitraryReplacementFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) RP η κ

/-- Naturality for arbitrary derived morphisms, represented only after replacement.
The equation for `replacementIso` is independent of the system resolutions; the
homotopy square also records the representative normalization involving both resolutions.
Source: Stacks 070I (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def DerivedNaturality : Prop :=
  DerivedNaturalityFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- Identity and cocycle laws for arbitrary changes of the simultaneous replacement.
System-resolution independence is already expressed by `ArbitraryReplacement` with
one fixed `replacementIso` for all `i`; the same Hom uniqueness applies to system
resolutions themselves, via the recorded K-injective Hom bijection.
Source: Stacks 070I (blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ResolutionCocycle : Prop :=
  ResolutionCocycleFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

attribute [local irreducible] RepresentativeShiftsFor

/-- The supplied shifted replacement is literally the shift, with the canonical
identity-component transport commuting restriction and limit with cochain translation.
The final homotopy says its comparison class is the shift of the original one.
Source: Stacks 070H, 070I, 070K and the cochain translation convention
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def RepresentativeShifts : Prop :=
  RepresentativeShiftsFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)




/-- The canonical supplied-replacement comparison commutes with every integer shift.
Both sides use precisely `v[r]`, transported only by the standard identity-component
commutation of termwise restriction with shifts. The coherent `CommShift` structures
include shift zero, addition, and consequently inverse shifts.
Source: Stacks 070K and 070Y
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def ReplacementShifts : Prop :=
  ReplacementShiftsFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)


/-- Changes of the `B`-system resolution satisfy the same cocycle and identity laws.
The formulas after ordinary direct image are formulas in the derived category,
so they are the change-of-model formulas for `Rp_*`.
Source: Stacks 070I and 0D6E
(blueprint: lem-pur-sequence-kinjective-comparison-shifts). -/
def SystemResolutionCocycle : Prop :=
  SystemResolutionCocycleFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

attribute [local semireducible] coefficientSequenceCommRingSheaf

set_option backward.isDefEq.respectTransparency true in
open SheafOfModules in
private theorem ringedSiteKInjectives
    {C : Type (t + 1)} [Category.{t} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u (t + 1)}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf J CommRingCat.{max u (t + 1)}) :
    Abelian.HasKInjectiveResolutions (SheafOfModules.{max u (t + 1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) := by
  let : IsGrothendieckAbelian.{max u (t + 1)} (SheafOfModules.{max u (t + 1)}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
      J R).1
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max u (t + 1)}

private instance sequenceKInjectives :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) := by
  let hsmall : EssentiallySmall.{max u (t + 1)} (ℕ × W.ProEt) :=
    coefficientSequenceEssentiallySmall.{t, u} W
  let : HasSheafify
      (coefficientSequenceTopology (AlgebraicGeometry.Scheme.ProEt.topology W))
      AddCommGrpCat.{max u (t + 1)} :=
    @SheafOfModules.hasSheafify_coefficientUniverse.{t + 1, t, max u (t + 1)}
      (ℕ × W.ProEt) inferInstance hsmall _
  let : (coefficientSequenceTopology
      (AlgebraicGeometry.Scheme.ProEt.topology W)).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{t + 1, t, max u (t + 1)}
      (ℕ × W.ProEt) inferInstance hsmall _
  exact ringedSiteKInjectives
    (coefficientSequenceTopology (AlgebraicGeometry.Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)


private abbrev strictEquivalence :=
  (SheafOfModules.strictSystemSequenceEquivalence (coefficientSequenceCommRingSystem l E W)).symm

private instance strictEquivalence_additive :
    (strictEquivalence l E W).functor.Additive where
  map_add := by
    intro M N f g
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    have h := (SheafOfModules.systemEvaluation
      (coefficientSequenceCommRingSystem l E W) n).map_add
        (f := (strictEquivalence l E W).functor.map f)
        (g := (strictEquivalence l E W).functor.map g)
    refine Eq.trans ?_ h.symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl

private theorem restriction_as_strict :
    (strictEquivalence l E W).functor ⋙
      SheafOfModules.RestrictedTowerResolution.restrictionFunctor
        (completedIntegralCommRingSheafUnrestricted l E W)
        (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W) =
      coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro M n
    have hφ : SheafOfModules.systemSequenceVerticalRingMap
        (coefficientSequenceCommRingSystem l E W) n =
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change (scalarReductionRestriction l E W n).obj
        ((SheafOfModules.pushforward
          (SheafOfModules.systemSequenceVerticalRingMap
            (coefficientSequenceCommRingSystem l E W) n)).obj M) = _
    rw [hφ]
    rfl
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

private theorem limit_restriction_acyclic
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (restrict l E W).obj I ⟶ J) [QuasiIso j] :
    QuasiIso ((limitComplex l E W).map j) := by
  let F := (strictEquivalence l E W).functor
  let U := SheafOfModules.RestrictedTowerResolution.restrictionFunctor
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
  have hU : F ⋙ U = coefficientSequenceRestriction l E W := restriction_as_strict l E W
  let I' := (F.mapHomologicalComplex (.up ℤ)).obj I
  have : CochainComplex.IsKInjective I' := inferInstance
  let : (coefficientSequenceRestriction l E W).Additive :=
    coefficientSequenceRestriction_additive l E W
  let e : (U.mapHomologicalComplex (.up ℤ)).obj I' ≅ (restrict l E W).obj I :=
    (NatIso.mapHomologicalComplex (F := F ⋙ U)
      (G := coefficientSequenceRestriction l E W) (eqToIso hU) (.up ℤ)).app I
  have := (SheafOfModules.RestrictedTowerResolution.acyclicity
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
    (𝟙 I') (e.hom ≫ j)).1
  have hc : QuasiIso ((limitComplex l E W).map e.hom ≫
      (limitComplex l E W).map j) := by
    simpa only [limitComplex, Functor.map_comp] using this
  exact (quasiIso_iff_comp_left
    ((limitComplex l E W).map e.hom) ((limitComplex l E W).map j)).mp hc

attribute [local irreducible] coefficientSequenceCommRingSheaf

/-- The normalized quotient-projection comparison, on arbitrary replacements and shifts.

Source: Stacks 0D6E, 070I, 070K, 070Y and 079P; latest blueprint,
`sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, coefficient comparisons
(blueprint: lem-pur-sequence-kinjective-comparison-shifts).

Proof plan, following the node's seven steps:
1. Factor the ringed projection through `cA`. Its module direct images are the recorded
   exact restriction `U` and ordinary limit, hence their composite is `push`.
   Use lem-weil-pbc-exact-functor-derived-functor to identify `Ra_*` with `D(U)`.
   Lem-weil-pbc-ringed-topoi-derived-pushforward-composition supplies the comparison
   to `D(U) ⋙ Rlim` with its universal-unit normalization.
2. On a K-injective system `I`, the composition theorem says that `lim j` is a
   quasi-isomorphism for any replacement `j : UI → J`. Naturality of the derived
   limit unit and its invertibility at `J` give `Normalization`.
   Prop-pur-kinjective-resolutions-exist supplies enough resolutions on the constant
   ringed sequence site; lem-weil-pbc-kinjective-total-derived computes the unit at `J`.
3. For supplied `v` and any `i : N → I`, exactness of restriction makes `Ui` a
   quasi-isomorphism. Lem-sc-kinjective-quasi-iso-comparison lifts `[v][Ui]⁻¹`
   uniquely to a homotopy class `b`. Injectivity gives `b Ui ≃ v`, and cohomology
   proves that every representative of `b` is a quasi-isomorphism.
4. `replacementIso` is exactly the localization comparison, `Rlim[v]`, and the
   inverse derived unit at `J`. Naturality of the units gives the displayed formula
   with `lim b`, which is therefore a quasi-isomorphism. This construction uses `v`
   alone and is independent of `i`.
5. Represent any derived morphism on the K-injective targets by `t` and `s`.
   The same Hom injectivity gives `s b ≃ b' Ut`. Apply additive limit to this
   homotopy. Apply the same uniqueness three times for the cocycle, and with the
   identity for the identity law, for both kinds of resolutions.
6. Lem-sf-kinjective-replacement-triangulated makes all shifted resolutions valid.
   Restriction and limit commute with cochain shifts by the identity in every degree.
   Thus `lim(j[r])` has degree-i map `lim j^(i+r)` and differential sign `(-1)^r`.
   Shift a comparison homotopy with the same sign; uniqueness gives the class `b[r]`.
7. Compute derived shift comparisons on those representatives, using the coherent
   K-injective localization equivalence and lem-weil-pbc-kinjective-total-derived.
   Naturality descends to every derived map. Shift zero is identity, and the signs
   multiply as `(-1)^r (-1)^s = (-1)^(r+s)`, giving addition and inverse shifts.
   None of these arguments requires restriction to preserve K-injectives, exact
   arbitrary products, bounded inputs, or normalized inputs. -/
theorem sequenceKInjectiveComparisonShifts
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    (aW : W ⟶ AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of D.k)))
    [_hW : AlgebraicGeometry.LocallyOfFiniteType aW] [_hqW : AlgebraicGeometry.QuasiCompact aW]
    (S : CoefficientDerivedSystemCalculus l E W)
    (_coherence : CoefficientDerivedSystemCoherence l E W S) :
    ∃ (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
      (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RP) (sRP : RP.CommShift ℤ),
      RP.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ)) ∧
      (∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective],
        IsIso (η.app I)) ∧
      (fun [_s : RP.CommShift ℤ] ↦
        NatTrans.CommShift η ℤ ∧
        ∃! κ : RP ≅ coefficientSequenceLimit l E W,
          Normalization l E W RP η κ ∧ ArbitraryReplacement l E W RP η κ ∧
          NatTrans.CommShift κ.hom ℤ ∧ DerivedNaturality l E W ∧
          ResolutionCocycle l E W ∧ SystemResolutionCocycle l E W ∧
          RepresentativeShifts l E W ∧ ReplacementShifts l E W) (_s := sRP) := by
  exact genericComparison (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
    (limit_restriction_acyclic l E W)

end WeilConjectures.SequenceKInjectiveComparison
