/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Submission.WeilConjectures.Compactification.Defs
import Submission.WeilConjectures.Compactification.NagataCompactification
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import Submission.WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Submission.WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.Derived
import Submission.WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Submission.WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Submission.WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Submission.WeilConjectures.SixFunctors.OpenClosed.Complex
import Submission.WeilConjectures.SixFunctors.OpenClosed.Conservative
import Submission.WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparisonComposition
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
public import Submission.WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import Submission.WeilConjectures.Compactification.CategoryBaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import Mathlib.AlgebraicGeometry.Noetherian

import Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import Submission.WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import all Submission.WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Unbounded ordinary etale compact-support comparisons

Source: Stacks Project, Tags 0F7H--0F7L and 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons).

The candidates, common-refinement comparisons, and proper/open tower isomorphism are the
existing ordinary etale constructions. The definitions below assemble the specified tower
composition and transport the existing exchange to exact, termwise inverse image. The
statements supply coherence and equality with the bounded-below maps, on actual natural
transformations rather than just existence of unrelated isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section UnboundedFormalism

private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

private noncomputable def exact_pb_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z := f ≫ g)
    (hfg : fg = f ≫ g := by cat_disch) :
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)

private lemma exact_pb_comp_assoc
    (A : Type (u + 1)) [CommRing A] {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (exact_pb_comp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (exact_pb_comp A g h gh hgh).hom
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory =
      (exact_pb_comp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
          (exact_pb_comp A f g fg hfg).hom := by
  let B := ModuleCat.{u + 1} A
  have he : upperStarComp B fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (upperStar B h) (upperStarComp B f g fg hfg) =
      upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (upperStarComp B g h gh hgh) (upperStar B f) := by
    apply Iso.ext
    exact (upperStarComp_assoc' B f g h fg gh fgh hfg hgh hfgh).symm
  exact (derived_triangle_assoc (upperStar B h) (upperStar B g) (upperStar B f)
    (upperStar B gh) (upperStar B fg) (upperStar B fgh)
    (upperStarComp B g h gh hgh) (upperStarComp B f g fg hfg)
    (upperStarComp B fg h fgh hfgh)
    (upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) he).symm

private lemma exact_pb_comp_congr
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (d d' : X ⟶ Z)
    (hd : d = f ≫ g) (hd' : d' = f ≫ g)
    (M : DerivedCategoryModule A Z) :
    (exact_pb_comp A f g d hd).hom.app M =
      eqToHom (by rw [hd, hd']) ≫ (exact_pb_comp A f g d' hd').hom.app M := by
  subst hd hd'
  simp

private noncomputable def exact_pb_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma exact_pb_id_left
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A (𝟙 X) f f (Category.id_comp f).symm).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
        (exact_pb_id A X).hom = 𝟙 _ := by
  apply derived_unit_right
  rw [upperStarComp_id_left]
  apply Iso.ext
  ext M
  simp

private lemma exact_pb_id_right
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
      Functor.whiskerRight (exact_pb_id A Y).hom
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory = 𝟙 _ := by
  apply derived_unit_left
  rw [upperStarComp_id_right]
  apply Iso.ext
  ext M
  simp

private noncomputable def unboundedFormalism
    (A : Type (u + 1)) [CommRing A] : CompactSupportFormalism where
  obj X := DerivedCategoryModule A X
  category X := inferInstanceAs (Category.{u + 1} (DerivedCategoryModule A X))
  pb f := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  pbId X := exact_pb_id A X
  pbComp f g := exact_pb_comp A f g
  pbComp_assoc f g h M := by
    have hh := NatTrans.congr_app
      (exact_pb_comp_assoc A f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hh
    rw [← hh, exact_pb_comp_congr A f (g ≫ h) _ (f ≫ g ≫ h)
      (Category.assoc _ _ _) rfl]
    simp only [Category.assoc, Functor.comp_obj]
  pbId_comp f M := by
    have hh := NatTrans.congr_app (exact_pb_id_left A f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A (𝟙 _) f _ f rfl (Category.id_comp f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pbComp_id f M := by
    have hh := NatTrans.congr_app (exact_pb_id_right A f) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A f (𝟙 _) _ f rfl (Category.comp_id f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pf f := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  adj f := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  sh j hj := haveI := hj.out; (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  shAdj j hj := haveI := hj.out; (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction

private lemma derived_square_symm
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {P : C ⥤ D} {Q : D ⥤ F} {R : C ⥤ E} {S : E ⥤ F}
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : P ⋙ Q ≅ R ⋙ S) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]

private lemma open_exchange_mate_coefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction B r
          ).mapDerivedCategoryAdjunction
        (openImmersionLowerShriekUpperStarAdjunction B l
          ).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso B sq.toCommSq).inv)).natTrans := by
  let := isIso_openImmersionLowerShriekBaseChangeMap B sq
  have h := mateEquiv_eq_of_unit
    (openImmersionLowerShriekUpperStarAdjunction B r).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction B l).mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom)
    (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).inv) (fun K ↦ ?_)
  · exact (congrArg TwoSquare.natTrans ((mateEquiv _ _).symm_apply_eq.mpr h.symm)).symm
  have hK := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction B r)
    (openImmersionLowerShriekUpperStarAdjunction B l)
    (squareUpperStarIso B sq.toCommSq.flip)
    (asIso (openImmersionLowerShriekBaseChangeMap B sq.toCommSq))
    (unit_map_openImmersionLowerShriekBaseChangeMap_app B sq.toCommSq) K
  rewrite [squareUpperStarIso_flip, derived_square_symm] at hK
  exact hK.symm

private lemma unbounded_pb_comp'
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : f ≫ g = fg) :
    (unboundedFormalism A).pbComp' f g fg w = exact_pb_comp A f g fg w.symm := by
  subst w
  rw [ExchangeFormalism.pbComp'_rfl]
  rfl

private lemma unbounded_sq_iso
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} (sq : CommSq t l r b) :
    (unboundedFormalism A).sqIso t l r b sq.w =
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  apply Iso.ext
  simp only [ExchangeFormalism.sqIso, unbounded_pb_comp', exact_pb_comp,
    Functor.mapDerivedCategoryTriangleIso, exactDerivedSquareUpperStarIso,
    squareUpperStarIso, derived_iso_trans,
    derived_iso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]

private lemma unbounded_open_base_change
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    ((unboundedFormalism A).baseChange t l r b sq.w).natTrans =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).hom := by
  rw [ExchangeFormalism.baseChange, unbounded_sq_iso]
  exact (open_exchange_mate_coefficients (ModuleCat.{u + 1} A) sq).symm

private local instance unbounded_has_base_change
    (A : Type (u + 1)) [CommRing A] : (unboundedFormalism A).HasBaseChange where
  isIso_baseChange sq := by
    rw [unbounded_open_base_change A sq]
    infer_instance

private lemma unbounded_open_exchange
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := unboundedFormalism A) sq
    ((unboundedFormalism A).exchange t l r b sq.w).natTrans =
      openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) sq
  dsimp only [ExchangeFormalism.exchange, openImmersionLowerShriekLowerStarExchange]
  have hh : inv ((unboundedFormalism A).baseChange t l r b sq.w).natTrans =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change A sq]
    exact Iso.hom_inv_id _
  rw [hh]
  rfl

private local instance unbounded_has_proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (unboundedFormalism A).HasProperExchange where
  isIso_exchange sq := by
    rw [unbounded_open_exchange A sq]
    exact isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
      isAddTorsion_of_finite sq

section ExactOpenComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe vC vD vE uC uD uE wC wD wE

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end ExactOpenComposition

section IdentityComparisons
universe vC vD uC uD wC wD v w
attribute [local irreducible] Adjunction.mapDerivedCategoryAdjunction
end IdentityComparisons

section OpenCompositionComparisons

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction

end OpenCompositionComparisons

end UnboundedFormalism

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

section UnboundedBaseChange

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

end UnboundedBaseChange

section HorizontalPasting
universe v w
open TwoSquare
end HorizontalPasting

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

section BoundedBelowRestriction

open Abelian

section Proper
attribute [local irreducible] upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction Adjunction.mapDerivedCategoryPlusAdjunction

attribute [local irreducible] upperStar lowerStar
section ProperExchangeRestriction
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.rightDerivedFunctorPlusCompatibility
end ProperExchangeRestriction
end Proper
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorPlusCompatibility
section ExchangeRestriction

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryPlusAdjunction upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction
end ExchangeRestriction

section CompositionRestriction

-- Keep the sheaf adjunction abstract while comparing its derived units.
attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction

section BoundedOpenCompositor
attribute [local irreducible] Adjunction.mapDerivedCategoryPlusAdjunction
  upperStarLowerStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  Adjunction.derivedPlus Adjunction.mapDerivedCategoryAdjunction

end BoundedOpenCompositor

private noncomputable def native_unbounded_triangle_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cf ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cfg :=
  (unboundedFormalism A).compIso T

private noncomputable def native_bounded_triangle_iso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [(derivedPlusFormalism B).HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    rightDerivedLowerShriekOfCompactificationPlus B T.cf ⋙
      rightDerivedLowerShriekOfCompactificationPlus B T.cg ≅
      rightDerivedLowerShriekOfCompactificationPlus B T.cfg :=
  (derivedPlusFormalism B).compIso T

end CompositionRestriction

section CompositionPlus

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2
attribute [local irreducible] Compactification.ofComp Compactification.restrict
  Compactification.comp
attribute [local irreducible] native_unbounded_triangle_iso native_bounded_triangle_iso
  rightDerivedLowerShriekOfCompactificationPlusCompatibility

end CompositionPlus

end BoundedBelowRestriction

end AlgebraicGeometry.Etale
