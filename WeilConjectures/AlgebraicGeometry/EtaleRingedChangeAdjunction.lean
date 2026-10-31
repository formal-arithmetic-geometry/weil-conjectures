/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.SixFunctors.ResolvingDerivedAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
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
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-!
# Normalized ringed coefficient change on small etale sites

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 07A6 and 0D6E;
Modules on Sites, Tags 03CZ, 03D2, 03D3 and 03DA
(blueprint: lem-pur-etale-ringed-change-adjunction).

All derived categories are ordinary unbounded categories. The ring inverse image is
presented by its adjunction to the actual site pushforward. Module direct image and
pullback are Mathlib's constructions. In the identified-ring case pullback is exact,
so its canonical derived adjunction is the exact-left-adjoint construction.

## Main statements

- `resReflectsIsomorphisms`: conservative termwise restriction.
- `etaleRingedChangeAdjunction`: canonical coefficient-change square and its adjunct identity.
- `identityRingedCoefficientAdjunction`: normalized coefficient extension for any small site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c h r w u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.EtaleRingedChange

/-- The recorded underlying ring sheaf, with no change in coefficients.
Source: Stacks 03DA (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev ring {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) := derivedChangeRingIndependentCoefficients J R

/-- The recorded category of module sheaves.
Source: Stacks 03DA (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev Mod {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) := ringedSiteModules.{r} (ring R)

/-- Actual restriction of scalars for the given ring-sheaf map.
Source: Stacks 03CZ (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev res {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) : Mod S ⥤ Mod R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)

section Site
variable {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Exact restriction, using the recorded coefficient-adjunction theorem.
Source: Stacks 03CZ, 03DA (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance resLimits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (res a) :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod S)
  (sheafRingDerivedCoefficientAdjunction a).choose

/-- Exact restriction, using the recorded coefficient-adjunction theorem.
Source: Stacks 03CZ, 03DA (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance resColimits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteColimits (res a) :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod S)
  (sheafRingDerivedCoefficientAdjunction a).choose_spec.choose

/-- K-injective resolutions from the existing Grothendieck category theorem.
Source: Stacks 079P (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance moduleKInjectives (R : Sheaf J CommRingCat.{r}) :
    Abelian.HasKInjectiveResolutions (Mod R) :=
  letI := isGrothendieckAbelian_coefficientUniverse (ring R)
  inferInstance

/-- Termwise restriction reflects isomorphisms on the unbounded derived category.
Source: Stacks 03DA and 05RT (blueprint: lem-pur-etale-ringed-change-adjunction).

Proof: restriction leaves the underlying abelian sheaf unchanged and is exact, so
its cohomology is restriction of cohomology. The inverse of an invertible R-linear
map which is S-linear is S-linear, by applying the original map to s times an
inverse image. Hence restriction detects isomorphisms on all cohomology sheaves.
The cohomology criterion in the unbounded derived category gives the assertion. -/
theorem resReflectsIsomorphisms {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod S)] :
    (res a).mapDerivedCategory.ReflectsIsomorphisms := by
  sorry

end Site

section Etale
open AlgebraicGeometry
variable {U V : Scheme.{u}} (f : U ⟶ V)

/-- Base change between the actual small etale sites.
Source: Stacks 03D2 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev base := MorphismProperty.Over.pullback @Etale ⊤ f

/-- Continuity of base change on small etale sites.
Source: Stacks 03D2 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance baseContinuous : (base f).IsContinuous
    V.smallEtaleTopology U.smallEtaleTopology :=
  AlgebraicGeometry.Etale.isContinuous_overPullback f

/-- Direct image of ring sheaves on the actual small etale sites.
Source: Stacks 03D2 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev ringsPush := (base f).sheafPushforwardContinuous CommRingCat.{u + 1}
  V.smallEtaleTopology U.smallEtaleTopology

/-- The structural map of the ringed morphism, in direct-image form.
Source: Stacks 03D2, 03D3 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
def structural {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) :
    ring.{u + 1, u, u + 1} R ⟶ ((base f).sheafPushforwardContinuous RingCat.{u + 1}
      V.smallEtaleTopology U.smallEtaleTopology).obj (ring.{u + 1, u, u + 1} S) :=
  ⟨Functor.whiskerRight p.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The induced module direct image, rather than an arbitrary lift.
Source: Stacks 03D2 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev push {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : Mod.{u + 1, u, u + 1} S ⥤ Mod.{u + 1, u, u + 1} R :=
  pushforward.{u + 1} (F := base f) (structural f p)

/-- Existence of ordinary module pullback is supplied by the existing universe-general API.
Source: Stacks 03D7 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance pushRightAdjoint {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : (push f p).IsRightAdjoint :=
  module_pushforward_isRightAdjoint_of_universes.{u + 1, u, 0}
    (U := base f) (structural f p)

/-- Mathlib's ordinary module pullback for the structural ring map.
Source: Stacks 03D3 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev pull {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : Mod.{u + 1, u, u + 1} R ⥤ Mod.{u + 1, u, u + 1} S :=
  letI : (pushforward.{u + 1} (F := base f) (structural f p)).IsRightAdjoint :=
    pushRightAdjoint f p
  pullback.{u + 1} (F := base f) (structural f p)

/-- The actual ordinary pullback/direct-image adjunction.
Source: Stacks 03D3 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
abbrev adj {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : pull f p ⊣ push f p :=
  letI : (pushforward.{u + 1} (F := base f) (structural f p)).IsRightAdjoint :=
    pushRightAdjoint f p
  pullbackPushforwardAdjunction (F := base f) (structural f p)

/-- Additivity of the actual direct image.
Source: Stacks 03D2 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance pushAdditive {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : (push f p).Additive where
  map_add := rfl

/-- Additivity transported by the existing adjunction.
Source: Stacks 03D3 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance pullAdditive {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
    (p : R ⟶ (ringsPush f).obj S) : (pull f p).Additive :=
  (adj f p).left_adjoint_additive

variable (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
    Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (ar : Lr ⊣ ringsPush f)

/-- With the pulled-back ring identified, module pullback is exact.
Source: Stacks 03D2, 03D3, 03DA (blueprint: lem-pur-etale-ringed-change-adjunction).

Proof: the module pullback is the algebraic inverse image followed by extension
along the displayed ring isomorphism. On underlying abelian sheaves it is the
ordinary exact etale inverse image. The faithful exact forgetful functors detect
vanishing of kernels and cokernels, so this pullback preserves finite limits. -/
theorem pullLimits {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : Lr.obj R ≅ S) :
    PreservesFiniteLimits (pull f (ar.homEquiv R S c.hom)) := by
  sorry

/-- The exact ordinary inverse image, localized termwise.
Source: Stacks 06YY (blueprint: lem-pur-etale-ringed-change-adjunction). -/
def derivedPull {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : Lr.obj R ≅ S)
    [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} R)]
    [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} S)] :
    DerivedCategory (Mod.{u + 1, u, u + 1} R) ⥤ DerivedCategory (Mod.{u + 1, u, u + 1} S) :=
  letI := pullLimits f Lr ar c
  letI := (adj f (ar.homEquiv R S c.hom)).leftAdjoint_preservesColimits
  (pull f (ar.homEquiv R S c.hom)).mapDerivedCategory

/-- The exact-left-adjoint specialization of the canonical derived adjunction.
Source: Stacks 06YY, 07A6 (blueprint: lem-pur-etale-ringed-change-adjunction). -/
def derivedAdj {R : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
    {S : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}} (c : Lr.obj R ≅ S)
    [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} R)]
    [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} S)] :
    derivedPull f Lr ar c ⊣ (push f (ar.homEquiv R S c.hom)).rightDerivedFunctor :=
  letI := pullLimits f Lr ar c
  letI := (adj f (ar.homEquiv R S c.hom)).leftAdjoint_preservesColimits
  (adj f (ar.homEquiv R S c.hom)).mapDerivedCategoryRightDerivedAdjunction

variable {RU SU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}}
  {RV SV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}}
  (aU : RU ⟶ SU) (aV : RV ⟶ SV) (cR : Lr.obj RV ≅ RU) (cS : Lr.obj SV ≅ SU)
  [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} RU)]
  [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} SU)]
  [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} RV)]
  [HasDerivedCategory.{w} (Mod.{u + 1, u, u + 1} SV)]

/-- The canonical derived comparison obtained by exact localization of the ordinary one.
Source: Stacks 06YY (blueprint: lem-pur-etale-ringed-change-adjunction). -/
def derivedComparison
    (b : pull f (ar.homEquiv SV SU cS.hom) ⋙ res.{u + 1, u, u + 1} aU ≅
      res.{u + 1, u, u + 1} aV ⋙ pull f (ar.homEquiv RV RU cR.hom)) :
    derivedPull f Lr ar cS ⋙ (res.{u + 1, u, u + 1} aU).mapDerivedCategory ≅
      (res.{u + 1, u, u + 1} aV).mapDerivedCategory ⋙ derivedPull f Lr ar cR :=
  letI := pullLimits f Lr ar cR
  letI := pullLimits f Lr ar cS
  letI := (adj f (ar.homEquiv RV RU cR.hom)).leftAdjoint_preservesColimits
  letI := (adj f (ar.homEquiv SV SU cS.hom)).leftAdjoint_preservesColimits
  Functor.mapDerivedCategorySquareIso b

/-- The normalized etale ringed change-of-coefficients adjunction square.
The ordinary direct-image comparison is identity on sections. Its ordinary adjunction
mate fixes b; exact localization fixes the derived b, and the displayed Hom identity
uniquely fixes d. Thus neither comparison is an arbitrary natural isomorphism.
Source: Stacks 03D2, 03D3, 03DA, 06YY, 07A6 and 0D6E
(blueprint: lem-pur-etale-ringed-change-adjunction).

Proof: identify both ordinary pullbacks with inverse image, transporting the scalar
actions through cR and cS. The coefficient square makes identity on inverse images
linear. Direct image has the same sections on both routes, with actions induced by
the same ring map; this gives q. Both ordinary units forget to the same abelian-sheaf
unit, giving the unit equation. Pullback is exact, so localizing b computes its
canonical derived comparison on every complex. To construct d, compose the two
canonical direct-image composition comparisons for the commuting ringed square.
For an S_U-K-injective I, resolve its R_U-restriction by j:r_U I to J. Under q,
d is represented by F_R(j), which is a quasi-isomorphism by ringed direct-image
composition; restriction of I need not be K-injective. Represent t by a chain map
to I. Resolving-derived-adjunction normalization identifies both transposes with
the ordinary transposes followed by these resolution comparisons. The unit equation
and naturality of q give F_R(j) q_I r_V(F_S(t) eta_S), which is exactly the right side
of the displayed derived identity. K-injective representatives cover all derived
maps. Naturality and the adjunction bijection give uniqueness of d. None of these
arguments assumes flat coefficient maps, bounded complexes, or finite dimension. -/
theorem etaleRingedChangeAdjunction
    (hsq : Lr.map aV ≫ cS.hom = cR.hom ≫ aU) :
    ∃ q : push f (ar.homEquiv SV SU cS.hom) ⋙ res.{u + 1, u, u + 1} aV ≅
        res.{u + 1, u, u + 1} aU ⋙ push f (ar.homEquiv RV RU cR.hom),
      (∀ (N : Mod.{u + 1, u, u + 1} SU) (W : V.Etaleᵒᵖ)
        (x : N.val.obj ((base f).op.obj W)), (q.hom.app N).val.app W x = x) ∧
      ∃ b : pull f (ar.homEquiv SV SU cS.hom) ⋙ res.{u + 1, u, u + 1} aU ≅
          res.{u + 1, u, u + 1} aV ⋙ pull f (ar.homEquiv RV RU cR.hom),
        (∀ M : Mod.{u + 1, u, u + 1} SV,
          (res.{u + 1, u, u + 1} aV).map ((adj f (ar.homEquiv SV SU cS.hom)).unit.app M) ≫
              q.hom.app ((pull f (ar.homEquiv SV SU cS.hom)).obj M) =
            (adj f (ar.homEquiv RV RU cR.hom)).unit.app ((res.{u + 1, u, u + 1} aV).obj M) ≫
              (push f (ar.homEquiv RV RU cR.hom)).map (b.inv.app M)) ∧
        ∃! d : (push f (ar.homEquiv SV SU cS.hom)).rightDerivedFunctor ⋙
              (res.{u + 1, u, u + 1} aV).mapDerivedCategory ≅
            (res.{u + 1, u, u + 1} aU).mapDerivedCategory ⋙
              (push f (ar.homEquiv RV RU cR.hom)).rightDerivedFunctor,
          ∀ (M : DerivedCategory (Mod.{u + 1, u, u + 1} SV))
            (N : DerivedCategory (Mod.{u + 1, u, u + 1} SU))
            (t : (derivedPull f Lr ar cS).obj M ⟶ N),
            (derivedAdj f Lr ar cR).homEquiv _ _
                ((derivedComparison f Lr ar aU aV cR cS b).inv.app M ≫
                  (res.{u + 1, u, u + 1} aU).mapDerivedCategory.map t) =
              (res.{u + 1, u, u + 1} aV).mapDerivedCategory.map
                  ((derivedAdj f Lr ar cS).homEquiv _ _ t) ≫
                d.hom.app N := by
  sorry

end Etale
section Coefficients
open CategoryTheory.CochainPullback
variable {C : Type c} [Category.{h} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (Mod R)]
    [HasDerivedCategory.{w} (Mod S)]

/-- Additivity of identity-geometric direct image, which is exactly restriction.
Source: Stacks 03CZ (blueprint: lem-pur-etale-ringed-change-adjunction). -/
instance identityPushAdditive : (extensionPullback φ).V.Additive :=
  inferInstanceAs (res φ).Additive

/-- Identity-geometric ringed pullback and coefficient extension have the same
canonical derived adjunction, with its actual representative maps.

`extensionPullback φ` is the existing ringed identity-geometric morphism: its
inverse and direct images of sets are identity, its structural map is φ, its
module pullback is sheafified tensor, and its module direct image is restriction.
The two left universal pairs below present its ringed and coefficient derivations.
The right pair presents its ringed derived direct image. Their universal properties
are presentation data, imposing no flatness or boundedness assumption on φ or complexes.
The ordinary adjunction used in both normalizations is the existing unique one
with unit the sheafification of x mapped to 1 tensor x.

Source: Stacks 03CZ, 06YY, 07A6, 0FND and 0D6E
(blueprint: lem-pur-etale-ringed-change-adjunction).

Proof: identity-geometric direct image is exactly restriction of scalars and is
exact. Thus its right-derived universal pair is identified with termwise restriction,
with identity comparison on every K-injective. Ordinary identity-geometric module
pullback is the sheafified balanced tensor construction, so the two left-derived
pairs derive the same ordinary functor. Uniqueness of universal left-derived pairs
gives the counit-compatible i; on flat-term K-flat representatives both counits
are invertible, and the displayed equation makes i identity on that tensor complex.
The ordinary ringed transpose is evaluation at 1 tensor x, exactly the normalized
coefficient transpose. Resolving-derived-adjunction normalization with flat-term
K-flats and K-injective targets therefore gives the two displayed Hom formulas.
All derived morphisms have such representatives, so these formulas identify the
adjunctions. Taking transposes of identities gives the unit and counit equations.
In particular, the normalized coefficient unit after its K-flat comparison is the
localized ordinary unit, whose section formula is x mapped to 1 tensor x.
This applies to every small site, including the one-point and empty sites. -/
theorem identityRingedCoefficientAdjunction
    (LH Lφ : DerivedCategory (Mod R) ⥤ DerivedCategory (Mod S))
    (εH : DerivedCategory.Qh ⋙ LH ⟶
      (extensionPullback φ).L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εφ : DerivedCategory.Qh ⋙ Lφ ⟶
      (extensionPullback φ).L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLH : LH.IsLeftDerivedFunctor εH (HomotopyCategory.quasiIso (Mod R) (.up ℤ)))
    (hLφ : Lφ.IsLeftDerivedFunctor εφ (HomotopyCategory.quasiIso (Mod R) (.up ℤ)))
    (RH : DerivedCategory (Mod S) ⥤ DerivedCategory (Mod R))
    (ηH : (res φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RH)
    (hRH : RH.IsRightDerivedFunctor ηH (HomotopyCategory.quasiIso (Mod S) (.up ℤ))) :
    ∃ (i : LH ≅ Lφ) (j : RH ≅ (res φ).mapDerivedCategory),
      (∀ H : HomotopyCategory (Mod R) (.up ℤ),
        i.hom.app (DerivedCategory.Qh.obj H) ≫ εφ.app H = εH.app H) ∧
      (∀ (P : CochainComplex (Mod R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
        IsIso (εH.app ((HomotopyCategory.quotient _ _).obj P)) ∧
          IsIso (εφ.app ((HomotopyCategory.quotient _ _).obj P))) ∧
      (∀ (I : CochainComplex (Mod S) ℤ), I.IsKInjective →
        IsIso (ηH.app ((HomotopyCategory.quotient _ _).obj I)) ∧
        ηH.app ((HomotopyCategory.quotient _ _).obj I) ≫
            j.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) ≫
            (res φ).mapDerivedCategoryFactorsh.hom.app
              ((HomotopyCategory.quotient _ _).obj I) = 𝟙 _) ∧
      ∃ (aH : LH ⊣ RH) (aφ : Lφ ⊣ (res φ).mapDerivedCategory),
        (∀ (M : DerivedCategory (Mod R)),
          aH.unit.app M ≫ RH.map (i.hom.app M) ≫ j.hom.app (Lφ.obj M) =
            aφ.unit.app M) ∧
        (∀ (N : DerivedCategory (Mod S)),
          LH.map (j.hom.app N) ≫ i.hom.app ((res φ).mapDerivedCategory.obj N) ≫
            aφ.counit.app N = aH.counit.app N) ∧
        (∀ (P : CochainComplex (Mod R) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
          (∀ (I : CochainComplex (Mod S) ℤ), I.IsKInjective →
            ∀ t : ((extensionPullback φ).L.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient _ _).obj P) ⟶
                  (HomotopyCategory.quotient _ _).obj I,
              aH.homEquiv _ _
                  (εH.app ((HomotopyCategory.quotient _ _).obj P) ≫ DerivedCategory.Qh.map t) =
                DerivedCategory.Qh.map
                    (((extensionPullback φ).moduleAdj.mapHomotopyCategory (.up ℤ)).homEquiv
                      _ _ t) ≫ ηH.app ((HomotopyCategory.quotient _ _).obj I) ∧
              aφ.homEquiv _ _
                  (εφ.app ((HomotopyCategory.quotient _ _).obj P) ≫ DerivedCategory.Qh.map t) =
                DerivedCategory.Qh.map
                    (((extensionPullback φ).moduleAdj.mapHomotopyCategory (.up ℤ)).homEquiv
                      _ _ t) ≫ (res φ).mapDerivedCategoryFactorsh.inv.app
                        ((HomotopyCategory.quotient _ _).obj I)) ∧
          aφ.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
              (res φ).mapDerivedCategory.map
                (εφ.app ((HomotopyCategory.quotient _ _).obj P)) ≫
              (res φ).mapDerivedCategoryFactorsh.hom.app
                (((extensionPullback φ).L.mapHomotopyCategory (.up ℤ)).obj
                  ((HomotopyCategory.quotient _ _).obj P)) =
            DerivedCategory.Qh.map
              (((extensionPullback φ).moduleAdj.mapHomotopyCategory (.up ℤ)).unit.app
                ((HomotopyCategory.quotient _ _).obj P))) := by
  sorry

end Coefficients
end SheafOfModules.EtaleRingedChange
