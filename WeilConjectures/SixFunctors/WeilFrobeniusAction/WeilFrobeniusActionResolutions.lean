/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSite
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
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
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Frobenius action sites and unbounded resolutions

Source: latest blueprint, cor-coef-verdier-weil-equivariance, internal-Hom/evaluation
paragraph; native action-site refinement, steps 1--7; Stacks 015F, 06YS, 079P, 0G7E,
and 08BJ (blueprint: lem-sf-weil-frobenius-action-resolutions).

The small site is the existing bounded pro-etale category with lifted hom types.
It retains every bounded object, and hence all integer translates. Coefficients
and K-flatness reuse the recorded section-ring and module-sheaf interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u wA wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.WeilFrobeniusAction

/-- Postcomposition on the actual bounded weakly etale site.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def postcompose {T : Scheme.{u}} (g : T ≅ T) : T.ProEt ≌ T.ProEt :=
  MorphismProperty.Comma.mapRightIso (P := @WeaklyEtale) (Q := ⊤) (W := ⊤)
    (𝟭 Scheme.{u}) ((Functor.const _).mapIso g)

/-- A small model containing every bounded object and every integer translate.
Source: native action-site proof, step 1; the size convention
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Site (T : Scheme.{u}) := AsSmall.{u + 1} T.ProEt

/-- The topology transported from the recorded small pro-etale site.
Source: native action-site proof, steps 1--2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev topology (T : Scheme.{u}) : GrothendieckTopology (Site T) :=
  AsSmall.down.inducedTopology (Scheme.ProEt.topology T)

/-- Inverse Frobenius translation, so inverse reindexing is geometric Frobenius pullback.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def translation {T : Scheme.{u}} (g : T ≅ T) : Site T ≌ Site T :=
  AsSmall.equiv.symm.trans ((postcompose g.symm).trans AsSmall.equiv)

private theorem kflat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {K L : CochainComplex (TwistedActionRingedSite.Modules R) ℤ} (e : K ≅ L)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) L := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF i
  exact (hK F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite (J := J) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) N := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M) at hM
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) N)
  exact (exactFunctor _ _).prop_of_iso
    ((SheafOfModules.siteSheafTensorRightIso R M) ≪≫
      ((MonoidalCategory.curriedTensor _).flip.mapIso e) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R N).symm) hM

set_option backward.isDefEq.respectTransparency false in
private theorem flat_comparison {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    SheafOfModules.IsFlat M ↔ SheafOfModules.IsFlatOnSite (J := J) (R := R) M := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight M) ↔
    exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M)
  exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm h,
    fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M) h⟩

end WeilConjectures.WeilFrobeniusAction
