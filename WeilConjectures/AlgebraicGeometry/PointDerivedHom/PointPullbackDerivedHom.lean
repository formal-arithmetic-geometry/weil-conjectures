/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import WeilConjectures.AlgebraicGeometry.ZetaWeil.ComponentRelativeProfiniteSite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.WContractibleComponentDerivedHom
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-! # Condensed-point pullback and unbounded derived internal Hom

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.1), and
its globalization over the w-contractible affine basis
(blueprint: lem-sfb-point-pullback-derived-hom).

## Main definitions and statements

- `comparison`: the canonical evaluation-adjoint map.
- `derivedRestrictionComparison`: canonical point-composition under restriction.
- `point_pullback_derived_hom`: invertibility, both naturalities and restriction equality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u c v d z a e w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PointDerivedHom

/-- Select data only from a unique, fully specified object.
Source: the canonical comparison specifications of Stacks 07A4 and HRS (4.1)
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def uniqueChoice {A : Sort a} {P : A → Prop} (h : ∃! x : A, P x) : A :=
  Classical.choose h.exists

/-- The canonical tensor comparison for the termwise functor of an exact inverse image.
The existing K-flat derived tensorator is transported through the canonical identification
of total left derivation with the exact termwise functor.
Source: Stacks 07A4 and 0G7D; HRS Section 3
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def exactTensor {C : Type c} [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{v + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat] :
    ExactDerivedTensorComparisonFamily F := fun K L ↦
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  e.symm.app (K ⊗ L) ≪≫
    asIso ((F.leftDerivedTensorComparison.app K).app L) ≪≫ tensorIso (e.app K) (e.app L)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing module-object inverse image from the condensed point.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
abbrev pull (X : Scheme.{u}) := (upperStarFromPoint X).mapMod Λ

/-- Left exactness is the recorded geometric inverse-image exactness.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pointLimits (X : Scheme.{u}) : PreservesFiniteLimits (upperStarFromPoint X) := by
  have : PreservesFiniteLimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.1
  unfold upperStarFromPoint
  infer_instance

/-- Colimits are preserved by the recorded point adjunction.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pointColimits (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u + 1, u + 1} (upperStarFromPoint X) :=
  (pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).leftAdjoint_preservesColimits

/-- The symmetric point inverse image with its existing tensorator.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pointBraided (X : Scheme.{u}) : (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

/-- Limits of module objects are computed on underlying sheaves.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pullLimits (X : Scheme.{u}) : PreservesFiniteLimits (pull Λ X) :=
  inferInstanceAs (PreservesFiniteLimits ((upperStarFromPoint X).mapMod Λ))

/-- Finite colimits of module objects are computed on underlying sheaves.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pullColimits (X : Scheme.{u}) : PreservesFiniteColimits (pull Λ X) :=
  inferInstanceAs (PreservesFiniteColimits ((upperStarFromPoint X).mapMod Λ))

/-- Additivity of the existing exact inverse image.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pullAdditive (X : Scheme.{u}) : (pull Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The ordinary balanced module tensorator of the point inverse image.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pullMonoidal (X : Scheme.{u}) : (pull Λ X).Monoidal :=
  Functor.monoidal_mapMod (upperStarFromPoint X)

/-- The ordinary uncompleted unbounded termwise derived inverse image.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
abbrev derivedPull (X : Scheme.{u}) := (pull Λ X).mapDerivedCategory

/-- The point adjunction lifted to modules supplies a genuine right adjoint.
Source: HRS Section 3 (blueprint: lem-sfb-point-pullback-derived-hom). -/
instance pullLeftAdjoint (X : Scheme.{u}) : (pull Λ X).IsLeftAdjoint :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).mapModAdjunction Λ).isLeftAdjoint

/-- Pullback from the condensed point preserves flat internal coefficient modules.
Source: Stacks 03EL, 07A4; HRS Section 3
(blueprint: lem-sfb-point-pullback-derived-hom).

Proof: use the internal-module/section-ring equivalence and the corresponding geometric
inverse image. A flat module is a filtered colimit of finite free modules locally on
the ringed site. Inverse image preserves these colimits and sends a finite free module
to the finite free module over the pulled-back ring. The resulting local filtered
colimit is flat. Equivalently the exact inverse image preserves the tensor tests for
flatness on local generators. The underlying coefficient and action maps are the
recorded mapMod construction, so transport back gives the asserted property. -/
@[instance] theorem pullFlat (X : Scheme.{u}) : (pull Λ X).PreservesFlat := by
  sorry

/-- The canonical K-flat derived tensor comparison transported to termwise pullback.
Its maps come from the existing normalized left-derived tensor comparison.
Source: HRS (4.1); Stacks 07A4, 0G7D
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def tensorComparison (X : Scheme.{u}) :
    ExactDerivedTensorComparisonFamily (pull Λ X) := exactTensor (pull Λ X)

/-- The type of comparisons of two internal Homs, with both inputs arbitrary.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def HomComparisonFamily {C : Type c} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C] {D : Type d} [Category.{z} D] [MonoidalCategory D]
    [MonoidalClosed D] (F : C ⥤ D) :=
  ∀ K L : C, F.obj ((ihom K).obj L) ⟶ (ihom (F.obj K)).obj (F.obj L)

/-- Evaluation-adjoint comparison for specified tensor comparison maps. This is an
actual transpose, and does not assume that it is invertible.
Source: Stacks 08J9 (blueprint: lem-sfb-point-pullback-derived-hom). -/
def evaluationComparison {C : Type c} [Category.{v} C] [MonoidalCategory C]
    [MonoidalClosed C]
    {D : Type d} [Category.{z} D] [MonoidalCategory D]
    [MonoidalClosed D] (F : C ⥤ D)
    (t : ∀ K L : C, F.obj (K ⊗ L) ≅ F.obj K ⊗ F.obj L) :
    HomComparisonFamily F := fun K L ↦
  MonoidalClosed.curry ((t K ((ihom K).obj L)).inv ≫ F.map ((ihom.ev K).app L))

/-- Transpose the exact derived tensor map using the existing native derived closedness.
Source: HRS (4.1), Stacks 08J9
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def exactEvaluation {C : Type c} [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{v + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (t : ExactDerivedTensorComparisonFamily F) : HomComparisonFamily F.mapDerivedCategory :=
  evaluationComparison F.mapDerivedCategory t

/-- Isomorphism and the two variances of a specified closed comparison.
Source: HRS Proposition 4.3(1); Stacks 08J9
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def PreservesHom {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type d} [Category.{z} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D)
    (b : ∀ K L : C, F.obj ((ihom K).obj L) ⟶ (ihom (F.obj K)).obj (F.obj L)) : Prop :=
  (∀ K L : C, IsIso (b K L)) ∧
  (∀ (K K' L : C) (a : K' ⟶ K),
    F.map ((MonoidalClosed.pre a).app L) ≫ b K' L =
      b K L ≫ (MonoidalClosed.pre (F.map a)).app (F.obj L)) ∧
  (∀ (K L L' : C) (a : L ⟶ L'),
    F.map ((ihom K).map a) ≫ b K L' = b K L ≫ (ihom (F.obj K)).map (F.map a))

/-- Equality under restriction of specified evaluation-adjoint comparisons, including
invertibility of the canonical Hom restriction identification on the two inputs.
Source: Stacks 08JB and 08J9; HRS (4.1)
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def RestrictsHom {C : Type c} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    {D E : Type d} [Category.{z} D] [Category.{z} E]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalCategory E] [MonoidalClosed E]
    (F : C ⥤ D) (G : C ⥤ E) (r : D ⥤ E) (e : F ⋙ r ≅ G)
    (b : ∀ K L : C, F.obj ((ihom K).obj L) ⟶ (ihom (F.obj K)).obj (F.obj L))
    (b' : ∀ K L : C, G.obj ((ihom K).obj L) ⟶ (ihom (G.obj K)).obj (G.obj L))
    (h : ∀ K L : D, r.obj ((ihom K).obj L) ⟶ (ihom (r.obj K)).obj (r.obj L)) : Prop :=
  ∀ K L : C,
    IsIso (h (F.obj K) (F.obj L)) ∧
    r.map (b K L) ≫ h (F.obj K) (F.obj L) ≫
        (MonoidalClosed.pre (e.inv.app K)).app (r.obj (F.obj L)) ≫
        (ihom (G.obj K)).map (e.hom.app L) =
      e.hom.app ((ihom K).obj L) ≫ b' K L

/-- The comparison beta, defined before any invertibility assertion. Its right-tensor
transpose is the inverse tensor comparison followed by pullback of evaluation.
The native left-tensor adjunction writes K first; symmetry writes the same map with
the Hom factor first as in the source, using the native Koszul braidings.
Source: HRS Proposition 4.3(1), (4.1); Stacks 08J9
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def comparison (X : Scheme.{u}) : HomComparisonFamily (derivedPull Λ X) :=
  exactEvaluation (pull Λ X) (tensorComparison Λ X)

/-- Ordinary point-composition comparison families, with the actual coefficient transport.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def PointCompositionFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pull Λ Y ⋙ CondensedRing.supportPullback Λ f ≅ pull Λ X

/-- Underlying-sheaf normalization of the ordinary point-composition map.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def PointCompositionNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : PointCompositionFamily Λ f) : Prop :=
  ∀ M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
    (e.hom.app M).hom = (upperStarFromPointComp f).hom.app M.X

/-- The ordinary point-composition comparison, including coefficient transport,
is uniquely determined by its underlying abelian-sheaf map.
Source: HRS (4.1), and the recorded profinite-point composition comparisons
(blueprint: lem-sfb-point-pullback-derived-hom).

Proof: lift the monoidal comparison upperStarFromPointComp f to module objects.
Transport the coefficient action along the inverse of its component at Lambda, exactly
as in supportPullback. Monoidality proves linearity of every component, and naturality
on sheaves proves naturality on modules. The inverse sheaf map gives the inverse module
map. The forgetful functor is faithful, so the stated underlying maps determine the
natural isomorphism uniquely. -/
theorem restrictionComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : PointCompositionFamily Λ f, PointCompositionNormalization Λ f e := by
  sorry

/-- Type of canonical composition identifications after exact localization.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def DerivedCompositionFamily {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{v} C]
    {D : Type d} [Category.{z} D] [Abelian D] [HasDerivedCategory.{z} D]
    {E : Type e} [Category.{w} E] [Abelian E] [HasDerivedCategory.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :=
  F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory

/-- Localize an ordinary composition isomorphism of exact functors.
Source: HRS (4.1), termwise localization
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def localizeComposition {C : Type c} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{v} C]
    {D : Type d} [Category.{z} D] [Abelian D] [HasDerivedCategory.{z} D]
    {E : Type e} [Category.{w} E] [Abelian E] [HasDerivedCategory.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (h : F ⋙ G ≅ H) :
    DerivedCompositionFamily F G H :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫ Functor.mapDerivedCategoryNatIso h

/-- The ordinary comparison uses the actual point-composition map on underlying sheaves.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def restrictionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) : PointCompositionFamily Λ f :=
  uniqueChoice (restrictionComparison_existsUnique Λ f)

/-- Termwise localization of the coefficient-normalized point-composition comparison.
Source: HRS (4.1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def derivedRestrictionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCompositionFamily (pull Λ Y) (CondensedRing.supportPullback Λ f) (pull Λ X) :=
  localizeComposition (pull Λ Y) (CondensedRing.supportPullback Λ f) (pull Λ X)
    (restrictionComparison Λ f)

/-- The canonical Hom comparison for restriction: the transpose of restricted evaluation
with the recorded, normalized derived tensor comparison. For a pro-etale test it is the
slice-restriction isomorphism, under the site and coefficient identifications.
Source: Stacks 08JB, 08J9; HRS (4.1)
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def restrictionHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HomComparisonFamily (CondensedRing.supportPullback Λ f).mapDerivedCategory :=
  exactEvaluation (CondensedRing.supportPullback Λ f)
    (CondensedRing.supportDerivedTensorComparison Λ f)

/-- Preservation of closedness for an exact functor with its specified Hom map.
Source: HRS Proposition 4.3(1) (blueprint: lem-sfb-point-pullback-derived-hom). -/
def ExactPreservesHom {C : Type c} [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type d} [Category.{v + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (b : HomComparisonFamily F.mapDerivedCategory) : Prop :=
  PreservesHom F.mapDerivedCategory b

/-- Exact-functor specialization of the canonical derived restriction square.
Source: HRS (4.1); Stacks 08JB and 08J9
(blueprint: lem-sfb-point-pullback-derived-hom). -/
def ExactRestrictsHom
    {C : Type c} [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {D E : Type d} [Category.{v + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    [Category.{v + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{v + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
    [MonoidalClosed E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
    (F : C ⥤ D) (G : C ⥤ E) (r : D ⥤ E)
    [F.Additive] [G.Additive] [r.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (e : DerivedCompositionFamily F r G)
    (b : HomComparisonFamily F.mapDerivedCategory)
    (b' : HomComparisonFamily G.mapDerivedCategory)
    (h : HomComparisonFamily r.mapDerivedCategory) : Prop :=
  RestrictsHom F.mapDerivedCategory G.mapDerivedCategory r.mapDerivedCategory e b b' h

/-- Condensed-point pullback preserves all unbounded derived internal Homs, with
contravariant/covariant naturality and equality of the canonical maps after restriction.
Source: HRS Proposition 4.3(1), (4.1), globalized over the w-contractible affine basis;
Stacks 08JB and 08J9 (blueprint: lem-sfb-point-pullback-derived-hom).

Proof:
1. The internal-module/section-ring equivalence fixes underlying sheaves and maps.
   The module-object derived comparison and internal-section tensor comparison identify
   the native tensors, Homs, and evaluation with their K-flat/K-injective ringed-site
   models, on the scheme, its slices, and the condensed point.
2. Pull back evaluation and transpose through the tensor-Hom adjunction. This is exactly
   comparison above. Naturality of evaluation and tensor descent gives both naturalities.
3. For every pro-etale test W, weakly-etale localization identifies the slice with W_proet.
   Coefficient-sections localization identifies its coefficient with p_W^*Lambda, and
   profinite-point composition gives derivedRestrictionComparison. The slice evaluation
   transpose theorem identifies restrictionHom with the canonical restriction isomorphism.
   Monoidal composition and uniqueness of transposes give the displayed equality of maps.
4. If W is w-contractible affine and S=pi_0(W), factor p_W through the profinite slice
   over S. The profinite slice comparison preserves Hom by Stacks 08JB, with evaluation
   normalization supplied by the slice transpose theorem.
5. The w-contractible component derived-Hom theorem applies to the two restricted
   unbounded objects over the arbitrary condensed ring. Its comparison, composed with
   the slice comparison, has precisely the defining transpose of comparison at W.
   Thus comparison at W is invertible without finiteness or boundedness conditions.
6. Restrict a cone of comparison at X to this affine covering basis. By steps 3--5 it
   vanishes there. Exact restriction commutes with every cohomology sheaf; separatedness
   on the covering basis kills each such sheaf globally. Thus the cone is zero in the
   ordinary unbounded category, proving invertibility. Empty X gives the zero category;
   zero inputs, arbitrary shifts and unbounded objects require no change. -/
theorem point_pullback_derived_hom (X : Scheme.{u}) :
    ExactPreservesHom (pull Λ X) (comparison Λ X) ∧
      ∀ W : X.ProEt,
        ExactRestrictsHom
          (C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
          (D := CondensedRing.supportModules Λ X)
          (E := CondensedRing.supportModules Λ W.left)
          (pull Λ X) (pull Λ W.left)
          (CondensedRing.supportPullback Λ W.hom)
          (derivedRestrictionComparison Λ W.hom)
          (comparison Λ X) (comparison Λ W.left) (restrictionHom Λ W.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.PointDerivedHom
