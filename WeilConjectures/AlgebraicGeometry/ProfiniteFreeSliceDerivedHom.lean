/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.CondensedInternalBarResolution
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleRestrictionInjectives
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.CoefficientSectionsLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-! # Profinite free modules and unbounded derived slice Hom

Source: Stacks Project, Cohomology on Sites, Tags 08FI and 08J7;
Hemo--Richarz--Scholbach, Section 3, Example 3.1 and equation (4.1)
(blueprint: lem-sfb-profinite-free-slice-derived-hom).

The normalized comparison retains the universal free generators, an actual chain
isomorphism on K-injective representatives, and its derived localization square.
Every helper constructs data from the existing free adjunctions and inverse images.
`exists_comparison` states the identity on the ordinary unbounded derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

/-- The existing relative profinite test object X[P], including its projection to X.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev test : X.ProEt := (profiniteToProEtOf X).obj P
/-- The representable profinite parameter, lifted to the coefficient universe.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev parameter := ((coherentTopology Profinite.{u}).uliftYoneda.{u + 1}).obj P
/-- The representable sheaf of the actual object X[P] of the small pro-etale site.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev represented := ((Scheme.ProEt.topology X).uliftYoneda.{u + 1}).obj (test X P)
/-- The existing strong monoidal inverse image lifted to internal coefficient modules.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def pointModulePullback : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
    Internal Λ X := (upperStarFromPoint X).mapMod Λ
/-- The existing free condensed module on the representable profinite parameter.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev freeParameter := (Profinite.CondensedAction.InternalBar.free (Mon.mk Λ)).obj
  (parameter P)
/-- The actual pullback p_X^*(Λ[P]) of the free condensed module.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev pulledFree := (pointModulePullback Λ X).obj (freeParameter Λ P)
/-- The pulled-back free module concentrated in degree zero in the unbounded category.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev derivedFree := (DerivedCategory.singleFunctor (Internal Λ X) 0).obj
  (pulledFree Λ X P)

/-- The free internal B-module functor, using free abelian sheaves and Mod.free.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev localFree : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⥤ Internal Λ X :=
  Sheaf.composeAndSheafify (Scheme.ProEt.topology X) AddCommGrpCat.free.{u + 1} ⋙
    Mod.free (condensedRingObj Λ X)

/-- The composite free-forgetful adjunction, fixing all local generators.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def localFreeAdjunction : localFree Λ X ⊣
    Mod.forget (condensedRingObj Λ X) ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1}) :=
  (Sheaf.adjunction (Scheme.ProEt.topology X) AddCommGrpCat.adj.{u + 1}).comp
    (Mod.freeForgetAdjunction (condensedRingObj Λ X))

/-- The actual free internal module B[h_U] on the relative representable.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev freeOnTest := (localFree Λ X).obj (represented X P)

/-- The unit generator at the identity of P in the existing free condensed module.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def pointGenerator : (freeParameter Λ P).X.obj.obj (op P) :=
  (((Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk Λ)).unit.app
    (parameter P)).hom.app (op P)) (ULift.up (𝟙 P))

/-- The local generator indexed by an actual arrow V to U, from the free unit.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def testGenerator (V : X.ProEt) (a : V ⟶ test X P) :
    (freeOnTest Λ X P).X.obj.obj (op V) :=
  (((localFreeAdjunction Λ X).unit.app (represented X P)).hom.app (op V)) (ULift.up a)

/-- The canonical composite set inverse-image/direct-image adjunction from the point.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def setAdjunction :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u})
    (Scheme.ProEt.topology specZ)).comp
      (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- The existing composite abelian inverse-image/direct-image adjunction from the point.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def abelianAdjunction :=
  pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The existing internal module pullback along the projection of X[P].
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev restriction := CondensedRing.upperStar Λ (test X P).hom
/-- The full existing module direct image, including restriction of coefficient scalars.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev directImage := CondensedRing.lowerStar Λ (test X P).hom
/-- Pullback applied termwise to an unbounded cochain complex.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev restrictionComplex := (restriction Λ X P).mapHomologicalComplex (.up ℤ)
/-- Pullback then direct image applied termwise, with the original differential.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev sliceComplex := ((restriction Λ X P) ⋙ directImage Λ X P).mapHomologicalComplex
  (.up ℤ)
/-- Exact pullback followed by K-injective total right derived direct image.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev sliceDerived := (restriction Λ X P).mapDerivedCategory ⋙
  CondensedRing.moduleObjectDerivedPushforward Λ (test X P).hom
/-- The ordinary complex concentrated in degree zero on p_X^*(Λ[P]).
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev freeComplex := (HomologicalComplex.single (Internal Λ X) (.up ℤ) 0).obj
  (pulledFree Λ X P)
/-- The actual section-module equivalence applied to the free complex.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev sectionFreeComplex := (complexForward Λ X).obj (freeComplex Λ X P)

/-- The canonical base change of V to U in the small pro-etale site of U.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev baseChanged (V : X.ProEt) : (test X P).left.ProEt :=
  (Scheme.proEtaleBaseChange (test X P).hom).obj V
/-- The base object V ×_X U, formed by the existing base change and composition functors.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
abbrev product (V : X.ProEt) : X.ProEt :=
  (MorphismProperty.Over.map (f := (test X P).hom) ⊤ (test X P).prop).obj
    (baseChanged X P V)

/-- The canonical projection V ×_X U to U, as an arrow over X.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def productToTest (V : X.ProEt) : product X P V ⟶ test X P :=
  MorphismProperty.Over.homMk (baseChanged X P V).hom rfl trivial

/-- The canonical section map M(V ×_X U) to (ρ_*ρ^*M)(V).
It is the module adjunction unit at the product followed by restriction along
the composition/base-change adjunction unit; hence it chooses no comparison map.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def sectionToSlice (M : Internal Λ X) (V : X.ProEt) :
    M.X.obj.obj (op (product X P V)) ⟶
      (((restriction Λ X P ⋙ directImage Λ X P).obj M).X.obj.obj (op V)) :=
  (((CondensedRing.upperStarLowerStarAdjunction Λ (test X P).hom).unit.app M).hom.hom.app
      (op (product X P V))) ≫
    ((restriction Λ X P).obj M).X.obj.map
      (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (test X P).hom
        (test X P).prop trivial).unit.app (baseChanged X P V)).op)

/-- The free generator transported through the inverse free-module identification
and the canonical degree-zero identification of the single complex.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def freeSectionGenerator
    (e : pulledFree Λ X P ≅ freeOnTest Λ X P)
    (V : X.ProEt) (a : V ⟶ test X P) :
    ((sectionFreeComplex Λ X P).X 0).val.obj (op V) :=
  (((equivalence Λ X).functor.map
    (e.inv ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (pulledFree Λ X P)).inv)).val.app (op V)) (testGenerator Λ X P V a)

/-- Free-generator evaluation of the degree n Hom-complex section.
Project onto the (0,n) Hom factor, restrict to V ×_X U over V, and apply the
resulting linear map to the generator indexed by the projection to U.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def evaluateHomSection (e : pulledFree Λ X P ≅ freeOnTest Λ X P)
    (J : CochainComplex (Internal Λ X) ℤ) (n : ℤ) (V : X.ProEt)
    (φ : ((homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
      ((complexForward Λ X).obj J)).X n).val.obj (op V)) :
    (J.X n).X.obj.obj (op (product X P V)) :=
  ((((WeilConjectures.coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X)
      (ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J)
      n 0 n (zero_add n)).val.app (op V) φ).app
        (op (Over.mk ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
          (test X P).hom (test X P).prop trivial).counit.app V)))).hom)
    (freeSectionGenerator Λ X P e (product X P V) (productToTest X P V))


/-- The canonical K-injective representative of Rρ_*ρ^* on Q(J).
It uses the exact-pullback localization factorization and the existing
right-derived-functor unit comparison on the K-injective restricted complex.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def derivedSliceModel (J : CochainComplex (Internal Λ X) ℤ)
    [CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J)] :
    (sliceDerived Λ X P).obj (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj ((sliceComplex Λ X P).obj J) :=
  (directImage Λ X P).rightDerivedFunctor.mapIso
      ((restriction Λ X P).mapDerivedCategoryFactors.app J) ≪≫
    (directImage Λ X P).rightDerivedFunctorObjQIso ((restrictionComplex Λ X P).obj J)

/-- Exactness of the point inverse image lifted to internal modules, needed for
its termwise derived functor and the final pullback-composition assertion.
Source: Stacks 03D2; HRS Section 3 and the exact inverse-image assertion of
lem-weil-pbc-profinite-point-pullback
(blueprint: lem-sfb-profinite-free-slice-derived-hom).
Proof: the point inverse image and scheme inverse image preserve finite limits
and finite colimits by lem-weil-pbc-profinite-point-pullback and
lem-weil-pbc-left-exact-site-inverse-image-tensor. Their composite does too.
The forgetful functors from internal modules create kernels and cokernels,
so mapMod preserves these finite limits and colimits. A functor between
abelian categories preserving finite products and the zero object is additive.
This supplies the exact additive functor used in step 7 of this node. -/
theorem pointModulePullback_exact : (pointModulePullback Λ X).Additive ∧
    PreservesFiniteLimits (pointModulePullback Λ X) ∧
      PreservesFiniteColimits (pointModulePullback Λ X) := by
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (abelianAdjunction X).leftAdjoint_preservesColimits
  have hcomm := ‹IsCommMonObj Λ›
  unfold pointModulePullback
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The additive structure supplied by the exact point-module pullback theorem.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
instance pointModulePullback_additive : (pointModulePullback Λ X).Additive :=
  (pointModulePullback_exact Λ X).1
/-- Finite-limit preservation supplied by the exact point-module pullback theorem.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
instance pointModulePullback_limits : PreservesFiniteLimits (pointModulePullback Λ X) :=
  (pointModulePullback_exact Λ X).2.1
/-- Finite-colimit preservation supplied by the exact point-module pullback theorem.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
instance pointModulePullback_colimits : PreservesFiniteColimits (pointModulePullback Λ X) :=
  (pointModulePullback_exact Λ X).2.2

/-- The specified module pullback-composition comparison, lifted termwise
to the ordinary unbounded derived categories. Its component at any N identifies
ρ^*p_X^*N with p_U^*N; there is no choice of a derived comparison.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def pointDerivedComposition
    (c : pointModulePullback Λ X ⋙ restriction Λ X P ≅
      pointModulePullback Λ (test X P).left) :
    (pointModulePullback Λ X).mapDerivedCategory ⋙
        (restriction Λ X P).mapDerivedCategory ≅
      (pointModulePullback Λ (test X P).left).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (pointModulePullback Λ X)
    (restriction Λ X P)).symm ≪≫ Functor.mapDerivedCategoryNatIso c

/-- The dependency’s evaluation-normalization square, expressed as a predicate.
The sectionwise tensor comparison carries the internal evaluation counit to
the ringed-site evaluation; no unnormalized choice of derived Hom is admitted.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
def homTransportNormalized
    (S : CoefficientClosedStructure (hom Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S)
    (t : TensorComparison Λ X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) : Prop :=
  ∀ K N : DerivedCategory (Internal Λ X),
    (forward Λ X).map
      ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
        (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
        (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
      t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
            (forward Λ X).obj K))
          (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
            (forward Λ X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
        S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)

/-- The full normalized assertions of the profinite free/slice calculation.
The tensor and Hom transport data are exactly those of the recorded comparison
dependency. `gamma` is a natural isomorphism of functors on the ordinary unbounded
derived category. The chain-level evaluation and localization fields fix its
normalization, including the original differential and the section-module encoding.
Source: Stacks 08FI, 08J7; HRS Section 3
(blueprint: lem-sfb-profinite-free-slice-derived-hom). -/
structure Comparison where
  /-- The inverse image of h_P is the representable h_U. -/
  setIso : (profinitePointSetSchemeInverseImage X).obj (parameter P) ≅ represented X P
  /-- Its adjunction transpose sends id_P to id_U, fixing every Yoneda generator. -/
  setGenerators :
    ((((setAdjunction X).unit.app (parameter P) ≫
      (Scheme.proEtaleSheafDirectImage (toSpecZ X) (Type (u + 1)) ⋙
        profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
          (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).map
            setIso.hom).hom.app (op P)) (ULift.up (𝟙 P))) =
        ULift.up (𝟙 (test X P))
  /-- Pullback of Λ[P] is the actual free B-module on h_U. -/
  freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P
  /-- The transpose sends the universal free generator to the same free generator. -/
  freeGenerators :
    ((((abelianAdjunction X).unit.app (freeParameter Λ P).X ≫
      (AlgebraicGeometry.ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar).map
        freeIso.hom.hom).hom.app (op P))
        (pointGenerator Λ P)) = testGenerator Λ X P (test X P) (𝟙 (test X P))
  /-- The ringed-site derived closed structure used by the recorded Hom comparison. -/
  closedStructure : CoefficientClosedStructure (hom Λ X)
  /-- Its actual K-flat tensor and K-injective Hom representative models. -/
  tensorModels : CoefficientTensorModels.{u, u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) closedStructure
  /-- The recorded tensor comparison with its pure-tensor normalization. -/
  tensorComparison : TensorComparison Λ X closedStructure tensorModels
  /-- The natural comparison of internal derived Hom with the ringed-site model. -/
  homComparison : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X
  /-- The comparison identifies the evaluation morphisms under the tensor comparison. -/
  homEvaluation : homTransportNormalized Λ X closedStructure tensorModels
    tensorComparison homComparison
  /-- The canonical derived isomorphism, natural in the entire unbounded derived input. -/
  gamma : (CondensedRing.derivedHom Λ X).obj (op (derivedFree Λ X P)) ≅
    sliceDerived Λ X P
  /-- The specified adjunction-unit section map is an isomorphism. -/
  sectionIdentification : ∀ (M : Internal Λ X) (V : X.ProEt),
    IsIso (sectionToSlice Λ X P M V)
  /-- Restriction to this site object preserves K-injective complexes. -/
  restrictionKInjective : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective],
    CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J)
  /-- The whole chain isomorphism on each K-injective representative. -/
  representative : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective],
    homComplex (R := ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J) ≅
      (complexForward Λ X).obj ((sliceComplex Λ X P).obj J)
  /-- In every degree and on every test object, the chain map is generator evaluation. -/
  evaluation : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective]
      (n : ℤ) (V : X.ProEt)
      (φ : ((homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
        ((complexForward Λ X).obj J)).X n).val.obj (op V)),
    (((representative J).hom.f n).val.app (op V)) φ =
      (sectionToSlice Λ X P (J.X n) V).hom (evaluateHomSection Λ X P freeIso J n V φ)
  /-- The natural derived isomorphism localizes that very chain map.
    Postcomposition with the canonical Hom resolution augmentation avoids any
    choice of inverse or unnormalized representative comparison. -/
  localization : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective]
      [CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J)],
    homComparison.hom.app (op (derivedFree Λ X P), DerivedCategory.Q.obj J) ≫
      (hom Λ X).map
        (X := (op ((forward Λ X).obj (derivedFree Λ X P)),
          (forward Λ X).obj (DerivedCategory.Q.obj J)))
        (Y := (op (DerivedCategory.Q.obj (sectionFreeComplex Λ X P)),
          DerivedCategory.Q.obj ((complexForward Λ X).obj J)))
        (Quiver.Hom.op ((localizationIso Λ X).inv.app (freeComplex Λ X P)),
          (localizationIso Λ X).hom.app J) ≫
      (WeilConjectures.coefficientHomResolutionIso.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) (sectionFreeComplex Λ X P)
          ((complexForward Λ X).obj J)).hom =
      (forward Λ X).map (gamma.hom.app (DerivedCategory.Q.obj J)) ≫
        (forward Λ X).map (derivedSliceModel Λ X P J).hom ≫
        (localizationIso Λ X).hom.app ((sliceComplex Λ X P).obj J) ≫
        DerivedCategory.Q.map (representative J).inv ≫
        DerivedCategory.Q.map
          (((homComplexFunctor (R := ring Λ X)).obj (op (sectionFreeComplex Λ X P))).map
            ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules Λ X)).app
              ((complexForward Λ X).obj J)))
  /-- The module inverse-image composition comparison from the condensed point. -/
  pointComposition : pointModulePullback Λ X ⋙ restriction Λ X P ≅
    pointModulePullback Λ (test X P).left
  /-- After forgetting modules it is the specified abelian composition comparison. -/
  pointComposition_underlying : ∀ M : Mod (Sheaf (coherentTopology Profinite.{u})
      Ab.{u + 1}) Λ,
    (pointComposition.hom.app M).hom =
      (profinitePointModuleForgetPullbackIso Λ (test X P).hom).hom.app
          ((pointModulePullback Λ X).obj M) ≫
        (upperStarFromPointComp (test X P).hom).hom.app M.X


/-- Relative profinite free modules and the normalized unbounded derived slice Hom identity.

Source: Stacks Project, Tags 08FI and 08J7; Hemo--Richarz--Scholbach,
Example 3.1 and (4.1) (blueprint: lem-sfb-profinite-free-slice-derived-hom).

Proof, following the seven steps of the node:
1. The relative profinite test-object functor preserves finite limits and covers
   (lem-weil-pbc-profinite-test-object-functor). Its inverse image is left adjoint
   to evaluation on X[Q] (lem-weil-pbc-left-exact-site-inverse-image-tensor and
   sk-def-sfb-pullback-from-point). Representables are sheaves by fpqc descent
   (lem-weil-pbc-fpqc-representable-descent). The two adjunction/Yoneda bijections
   give Hom(p_X^(-1)h_P,G) = G(X[P]) = Hom(h_U,G). Evaluation at id_P identifies
   the universal generators, so the inverse Yoneda maps are identities
   (lem-galois-yoneda-hom-bijection).
2. Compose the free adjunction (def-sfb-condensed-free-module-generators) with
   the monoidal module adjunction (sk-def-sfb-transport). Maps from p_X^*Λ[P]
   are maps from p_X^(-1)h_P into the underlying sheaf. Step 1 therefore identifies
   it with B[h_U], with exactly the displayed universal-generator normalization.
3. Sheaf Hom on V is Hom on the slice over V (def-pur-sheaf-hom). Restriction is
   the set inverse image (lem-sfb-proetale-object-inverse-image-restriction), and
   coefficient localization identifies module pullback with restriction
   (lem-sfb-coefficient-sections-localization and sk-def-sfb-module-pushforward-pullback).
   Its right adjoint commutes with forgetting modules. Compose left adjoints
   as in step 2 to see that the restricted module is free on h_U restricted to V.
   This sheaf is represented by V ×_X U. Free adjunction and Yoneda give
   Hom(B[h_U],M)(V) = M(V ×_X U), evaluating at the projection generator.
   The inverse sends a generator a:W→U to restriction along (v_W,a).
   The maps respect scalars, restrictions, and module morphisms. In the actual
   upper/lower-star model the identification is sectionToSlice, the unit followed
   by the canonical base-change graph restriction.
4. U is weakly etale (lem-weil-pbc-profinite-test-object-functor). Its site is
   the slice (lem-weil-pbc-proetale-restriction-injectives, site clause only).
   Coefficient localization makes ρ^* the exact restriction functor, so its left
   derived functor is termwise pullback (sk-def-sfb-derived-categories).
   Choose a K-injective representative J (prop-pur-kinjective-resolutions-exist).
   The exact extension-by-zero/restriction adjunction
   (lem-pur-kinjective-restrict-localized-adjunction-universes) and
   lem-pur-kinjective-restrict-localized-universes show J restricted to U is
   K-injective. Thus Rρ_*ρ^*K is represented by ρ_*(J restricted to U), with
   sections J(V ×_X U) (def-sfb-finite-lower-star and sk-def-sfb-module-derived-pushpull).
5. The degree n Hom complex from B[h_U][0] into J has only its (0,n) factor
   (def-pur-hom-complex); its differential is postcomposition by d_J.
   Step 3 in every degree is therefore a chain isomorphism, with unchanged
   differential. Localize it, using the K-injective model
   (def-pur-derived-internal-hom) and steps 2 and 4. The localization equation
   uses the fixed factorization and the fixed Hom-resolution augmentation,
   so it states the identity of derived objects with its actual normalization.
   Evaluation commutes with chain maps. K-injective representatives compute
   derived morphisms, giving naturality in K and independence of representatives.
6. The exact internal/section module equivalence
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence) leaves sections and
   maps unchanged. Its tensor comparison fixes local pure tensors
   (lem-pe-internal-section-tensor-comparison). The evaluation-normalized
   derived Hom comparison (lem-sfb-module-object-ringed-site-derived-comparison)
   and operation transport (lem-sfb-internal-module-operations-transport)
   identify both calculations. Exact equivalences preserve K-injectives by
   transporting the acyclic-Hom test through their exact inverse. Consequently
   the chain evaluation, scalar actions, differentials and localized gamma agree.
7. The monoidal comparison upperStarFromPointComp from
   lem-weil-pbc-profinite-point-pullback lifts to modules and identifies
   ρ^*p_X^* with p_U^*. Its normalized underlying map is specified here;
   pointDerivedComposition lifts this same isomorphism termwise, hence gives
   the asserted comparison for every unbounded N, with no new choice. -/
theorem exists_comparison : Nonempty (Comparison Λ X P) := by
  sorry

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
