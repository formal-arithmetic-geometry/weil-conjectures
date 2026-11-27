/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
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
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
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
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck

import WeilConjectures.SixFunctors.Coefficient.CoefficientActualScalarDerivedPair
import WeilConjectures.CategoryTheory.ScalarHomTensor.PrescribedScalarTensorComparison
import WeilConjectures.Algebra.Homology.SixFunctors.SemilinearEvaluationAcyclicLift
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
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
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
/-! # Scalar foundation for coherent coefficient-system evaluation

This file contains the ordinary tower sections and limit projections, the scalar adjunction
and quotient comparison, the finite reduction representative, and the uniquely normalized
scalar tensor comparison used in the evaluation calculus of derived coefficient systems.

## Implementation details

This is the scalar foundation previously declared in
`WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus`,
which publicly re-exports it. The module split follows profiling and local unfolding
improvements.

## References

* Stacks Project, Cohomology on Sites, Tags 06YS, 0A95 and 0941; Injectives, Tag 079P.
* Stacks Project, Tags 03CZ, 03D7, 03DA, 03EK, 06YY, 07A4, 07A6, 08J9, 08JA, 0A98.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v a b r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

section StandardCoefficientInstances

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Derived termwise global sections, keeping the strict tower until after deriving. -/
noncomputable def coefficientTowerSections :
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource l E W)
    AddCommGrpCat.{max u (t+1)}).obj
      (coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W))

/-- Global sections on towers are additive, component by component. -/
theorem coefficientTowerSections_additive : (coefficientTowerSections l E W).Additive := by
  unfold coefficientTowerSections
  infer_instance

/-- Additivity needed for the total right derived tower-sections functor. -/
noncomputable instance coefficientTowerSectionsAdditive :
    (coefficientTowerSections l E W).Additive := coefficientTowerSections_additive l E W

attribute [local irreducible] preadditiveCoyoneda SheafOfModules.unit

/-- The standard derived category of strict abelian-group towers. -/
noncomputable instance coefficientAbTowersDerived :
    HasDerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) := HasDerivedCategory.standard _

/-- The standard derived category of the mapping complexes' abelian groups. -/
noncomputable instance coefficientAbDerived :
    HasDerivedCategory AddCommGrpCat.{r} := HasDerivedCategory.standard _

/-- Abelian-group towers admit simultaneous K-injective resolutions. -/
theorem coefficientAbTowers_haveKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) := by
  classical
  let G := separator AddCommGrpCat.{r}
  have hG := isSeparator_separator AddCommGrpCat.{r}
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint AddCommGrpCat.{r} n).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight AddCommGrpCat.{r} n
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{r, r} (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{r, r} (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
    { locallySmall := ⟨fun P Q ↦ small_of_injective
        (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }
  infer_instance

/-- Simultaneous K-injectives for the mapping-complex towers. -/
noncomputable instance coefficientAbTowersKInjectives :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) :=
  coefficientAbTowers_haveKInjectives.{r}

/-- Inverse limit of abelian-group towers preserves addition. -/
theorem coefficientAbLimit_additive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- Additivity for the mapping-complex total-limit functor. -/
noncomputable instance coefficientAbLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}).Additive :=
  coefficientAbLimit_additive.{r}

/-- The actual total right derived limit on mapping-complex towers. -/
noncomputable abbrev coefficientMappingLimit :
    DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      DerivedCategory AddCommGrpCat.{r} :=
  (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
    AddCommGrpCat.{r}).rightDerivedFunctor

/-- The derived evaluation on strict mapping-complex towers. -/
noncomputable abbrev coefficientMappingEvaluation (n : ℕ) :
    DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤
      DerivedCategory AddCommGrpCat.{r} :=
  ((evaluation ℕᵒᵖ AddCommGrpCat.{r}).obj (op n)).mapDerivedCategory

/-- Actual mapping-limit projections, fixed on simultaneous K-injective resolutions. -/
theorem coefficientMappingProjection_exists (n : ℕ) :
    ∃! π : coefficientMappingLimit.{r} ⟶ coefficientMappingEvaluation.{r} n,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ℤ) [I.IsKInjective],
        π.app (DerivedCategory.Q.obj I) ≫
          ((evaluation ℕᵒᵖ AddCommGrpCat.{r}).obj
            (op n)).mapDerivedCategoryFactors.hom.app I =
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{r}) ⥤ AddCommGrpCat.{r}) I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (ComplexShape.up ℤ)).app I) := by
  let A := ℕᵒᵖ ⥤ AddCommGrpCat.{r}
  let F : A ⥤ AddCommGrpCat.{r} := lim
  let E := (evaluation ℕᵒᵖ AddCommGrpCat.{r}).obj (op n)
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  have hd := CategoryTheory.derives F
  have : F.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (F.rightDerivedFunctorUnitQ I.obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let β := Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)) DerivedCategory.Q ≫
      E.mapDerivedCategoryFactors.inv
  let π := F.rightDerivedFunctor.rightDerivedDesc η
    (HomologicalComplex.quasiIso A (.up ℤ)) E.mapDerivedCategory β
  have hπ (I : CochainComplex A ℤ) [I.IsKInjective] :
      π.app (DerivedCategory.Q.obj I) ≫ E.mapDerivedCategoryFactors.hom.app I =
        (F.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (.up ℤ)).app I) := by
    apply (cancel_epi (F.rightDerivedFunctorObjQIso I).inv).mp
    rw [← F.rightDerivedFunctorUnitQ_eq]
    change η.app I ≫ (π.app _ ≫ _) = _
    rw [← Category.assoc, Functor.rightDerived_fac_app]
    simp [β, F.rightDerivedFunctorUnitQ_eq]
  refine ⟨π, hπ, ?_⟩
  intro π' hπ'
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  apply (cancel_mono (E.mapDerivedCategory.map e.hom)).mp
  rw [← π'.naturality, ← π.naturality]
  congr 1
  apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app I)).mp
  exact (hπ' I).trans (hπ I).symm

/-- The mapping-limit projection defined by its unique K-injective normalization. -/
noncomputable def coefficientMappingProjection (n : ℕ) :=
  (coefficientMappingProjection_exists.{r} n).choose

/-- The coherent global derived mapping-complex system `H_W`: termwise derived global
sections of the exact scalar restriction of the sequence-site internal Hom. -/
noncomputable def coefficientSequenceGlobalHom :
    (coefficientSequenceDerived l E W)ᵒᵖ × coefficientSequenceDerived l E W ⥤
      DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{max u (t+1)}) :=
  coefficientSequenceInternalHom l E W ⋙ coefficientSequenceDerivedRestriction l E W ⋙
    (coefficientTowerSections l E W).rightDerivedFunctor
/-- The base-change map in the derived categories, defined by evaluation and tensor-Hom
transposition. -/
def coefficientBaseChangeHom
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    F.obj (HA.obj (op P, Q)) ⟶ HB.obj (op (F.obj P), F.obj Q) :=
  SB.transpose _ (F.obj P) (F.obj Q)
    (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q))

/-- Coherence of an evaluation-defined comparison, as system-map equations: naturality,
compatibility with tensor-Hom transposes, and compatibility with internal composition. -/
structure CoefficientEvaluationCompatible
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop where
  /-- Naturality in both derived inputs. -/
  naturality : ∀ (P Q P' Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q'),
    F.map (HA.map
        (Prod.mkHom (f.op) (g))) ≫ coefficientBaseChangeHom SA SB F μ P' Q' =
      coefficientBaseChangeHom SA SB F μ P Q ≫ HB.map
        (Prod.mkHom ((F.map f).op) (F.map g))
  /-- Compatibility with every tensor-Hom transpose, before evaluation at a level. -/
  transpose : ∀ (T P Q : A) (f : SA.tensor.obj (T, P) ⟶ Q),
    F.map (SA.transpose T P Q f) ≫ coefficientBaseChangeHom SA SB F μ P Q =
      SB.transpose (F.obj T) (F.obj P) (F.obj Q) (μ.inv.app (T, P) ≫ F.map f)
  /-- Compatibility with internal composition as a system morphism. -/
  composition : ∀ P Q V : A,
    F.map (SA.composition P Q V) ≫ coefficientBaseChangeHom SA SB F μ P V =
      μ.hom.app (HA.obj (op Q, V), HA.obj (op P, Q)) ≫
        SB.tensor.map
        (Prod.mkHom (coefficientBaseChangeHom SA SB F μ Q V)
          (coefficientBaseChangeHom SA SB F μ P Q)) ≫
        SB.composition (F.obj P) (F.obj Q) (F.obj V)

/-- The enriched adjunction map: the adjunct of base change followed by internal Hom of
the counit. -/
def coefficientEnrichedAdjunctionMap
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P : A) (N : B) :
    HA.obj (op P, G.obj N) ⟶ G.obj (HB.obj (op (F.obj P), N)) :=
  adj.homEquiv _ _
    (coefficientBaseChangeHom SA SB F μ P (G.obj N) ≫
      HB.map
        (Prod.mkHom (𝟙 _) (adj.counit.app N)))

private theorem restrictScalars_comp_eq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{w} g ⋙ SheafOfModules.restrictScalars.{w} f =
      SheafOfModules.restrictScalars.{w} (f ≫ g) := by
  exact Functor.ext_of_iso (normalizedDVRRestrictionCompIso f g)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Successive coefficient restrictions equal restriction by the limit projection. -/
theorem coefficientRestrictionComp {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m =
      scalarReductionRestriction l E W n := by
  let p (k : ℕ) := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W k)
  have hπ : p m ≫ normalizedDVRQuotient l E W h = p n :=
    limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op
  exact (restrictScalars_comp_eq (p m) (normalizedDVRQuotient l E W h)).trans
    (congrArg SheafOfModules.restrictScalars hπ)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

section QuotientNaturality

/-- The natural mate of a comparison between composite right adjoints. -/
noncomputable def coefficientQuotientNatTrans
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} C]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {F' : A ⥤ C} {G' : C ⥤ A} (adj' : F' ⊣ G')
    (U : C ⥤ B) (e : U ⋙ G ≅ G') : F ⟶ F' ⋙ U where
  app M := (adj.homEquiv M (U.obj (F'.obj M))).symm
    (adj'.unit.app M ≫ e.inv.app (F'.obj M))
  naturality {M N} f := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hn : f ≫ adj'.unit.app N = adj'.unit.app M ≫ G'.map (F'.map f) :=
      adj'.unit.naturality f
    erw [← Category.assoc, hn]
    exact (Category.assoc _ _ _).trans
      ((congrArg (adj'.unit.app M ≫ ·) (e.inv.naturality (F'.map f))).trans
        (Category.assoc _ _ _).symm)

/-- The ordinary scalar adjunction, named before taking its components. -/
noncomputable def coefficientOrdinaryScalarAdjunction (n : ℕ) :
    scalarReductionExtension l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

attribute [local irreducible] coefficientOrdinaryScalarAdjunction

/-- The natural scalar quotient map, before evaluating it at a module. -/
noncomputable def coefficientOrdinaryQuotientNaturalTransformation {m n : ℕ} (h : n ≤ m) :
    scalarReductionExtension l E W m ⟶
      scalarReductionExtension l E W n ⋙ normalizedDVRModuleRes l E W h :=
  coefficientQuotientNatTrans
    (coefficientOrdinaryScalarAdjunction l E W m)
    (coefficientOrdinaryScalarAdjunction l E W n)
    (normalizedDVRModuleRes l E W h) (eqToIso (coefficientRestrictionComp l E W h))

attribute [local irreducible] coefficientOrdinaryQuotientNaturalTransformation

/-- The ordinary tensor quotient map, as the scalar-extension adjunct of `x ↦ x ⊗ 1`. -/
noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  (coefficientOrdinaryQuotientNaturalTransformation l E W h).app M

attribute [local irreducible] scalarReductionExtension

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary quotient components form a unique natural transformation. -/
theorem coefficientOrdinaryQuotient_exists {m n : ℕ} (h : n ≤ m) :
    ∃! τ : scalarReductionExtension l E W m ⟶
      scalarReductionExtension l E W n ⋙ normalizedDVRModuleRes l E W h,
      ∀ M, τ.app M = coefficientOrdinaryQuotientComponent l E W h M := by
  refine ⟨coefficientOrdinaryQuotientNaturalTransformation l E W h, fun _ ↦ rfl, ?_⟩
  intro τ hτ
  exact NatTrans.ext (funext hτ)

end QuotientNaturality

/-- Strict quotient maps between the ordinary tensor reductions. -/
noncomputable def coefficientOrdinaryQuotient {m n : ℕ} (h : n ≤ m) :=
  (coefficientOrdinaryQuotient_exists l E W h).choose

/-- The additive structure of the ordinary finite scalar extension. -/
noncomputable instance coefficientFiniteExtensionAdditive (n : ℕ) :
    (scalarReductionExtension l E W n).Additive :=
  scalarReductionExtensionAdditive l E W n

/-- The universal counit of finite reduction is invertible on every K-flat
representative. -/
theorem coefficientFiniteReductionCounit_isIso
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) : IsIso ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q)) := by
  exact (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.2 Q hQ

/-- Localizing an invertible representative counit gives its canonical model
isomorphism. -/
noncomputable def coefficientLocalizedCounitModel
    {A : Type a} {B : Type b} [Category.{v} A] [Abelian A]
    [Category.{w} B] [Abelian B]
    [HasDerivedCategory.{r} A] [HasDerivedCategory.{c} B]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    (f : F.obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (.up ℤ)).obj Q))
    (hf : IsIso f) : F.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj Q :=
  F.mapIso ((DerivedCategory.quotientCompQhIso A).app P).symm ≪≫
    @asIso _ _ _ _ f hf ≪≫ (DerivedCategory.quotientCompQhIso B).app Q

attribute [local irreducible] coefficientLocalizedCounitModel

/-- The canonical computation of finite derived reduction on a K-flat complex. -/
noncomputable def coefficientFiniteReductionModel
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E W n).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  coefficientLocalizedCounitModel (coefficientFiniteDerivedExtension l E W n) Q
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
    ((scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))
    (coefficientFiniteReductionCounit_isIso l E W Q hQ n)

attribute [local irreducible] coefficientFiniteReductionModel

/-- A comparison between a composite of three arrows and a composite of two arrows. -/
def CoefficientComparisonEquation
    {D : Type a} [Category.{b} D] {X₀ X₁ X₂ X₃ X₄ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₄)
    (p : X₀ ⟶ X₃) (q : X₃ ⟶ X₄) : Prop := f ≫ g ≫ h = p ≫ q

/-- A comparison between two composites of two arrows. -/
def CoefficientTransitionEquation
    {D : Type a} [Category.{b} D] {X₀ X₁ X₂ X₃ : D}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₃) (p : X₀ ⟶ X₂) (q : X₂ ⟶ X₃) : Prop :=
  f ≫ g = p ≫ q

attribute [local irreducible] CoefficientComparisonEquation CoefficientTransitionEquation

/-- A chain comparison into a composite, with its target displayed termwise. -/
noncomputable def coefficientComplexCompositeTransformation
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{v} A] [HasZeroMorphisms A]
    [Category.{w} B] [HasZeroMorphisms B]
    [Category.{r} D] [HasZeroMorphisms D]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (G : B ⥤ D) [G.PreservesZeroMorphisms]
    {H : A ⥤ D} [H.PreservesZeroMorphisms] (τ : H ⟶ F ⋙ G)
    (P : CochainComplex A ℤ) :
    (H.mapHomologicalComplex (.up ℤ)).obj P ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P

attribute [local irreducible] coefficientComplexCompositeTransformation

/-- A chain comparison out of a composite, with its source displayed termwise. -/
noncomputable def coefficientComplexCompositeSourceTransformation
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{v} A] [HasZeroMorphisms A]
    [Category.{w} B] [HasZeroMorphisms B]
    [Category.{r} D] [HasZeroMorphisms D]
    (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (G : B ⥤ D) [G.PreservesZeroMorphisms]
    {H : A ⥤ D} [H.PreservesZeroMorphisms] (τ : F ⋙ G ⟶ H)
    (P : CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (H.mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex τ (.up ℤ)).app P

attribute [local irreducible] coefficientComplexCompositeSourceTransformation

/-- Simultaneous K-flat computation of reduction, with its strict quotient maps, compatible
at each level with the derived finite-reduction comparison. -/
def CoefficientReductionModels
    (R : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (ρ : ∀ n : ℕ, R ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
        (Q.X i)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : R.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C ≅ ((scalarReductionExtension l E W n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            Q),
      (∀ n : ℕ,
        CoefficientComparisonEquation
          ((coefficientSequenceDerivedEvaluation l E W n).map e.hom)
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C)
          (DerivedCategory.Q.map (κ n).hom)
          ((ρ n).hom.app (DerivedCategory.Q.obj Q))
          ((coefficientFiniteReductionModel l E W Q hQ n).hom)) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        CoefficientTransitionEquation
          (coefficientComplexCompositeTransformation
            (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
            (coefficientSequenceTransition l E W h) C)
          (((normalizedDVRModuleRes l E W h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (κ n).hom)
          ((κ m).hom)
          (coefficientComplexCompositeTransformation
            (scalarReductionExtension l E W n) (normalizedDVRModuleRes l E W h)
            (coefficientOrdinaryQuotient l E W h) Q))
/-- The pure-tensor formula for a scalar tensor comparison over general ring sheaves: the
chain isomorphism sends every scalar-unit tensor generator to the tensor of the scalar-unit
sections. -/
def CoefficientScalarTensorGenerators
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A B : Sheaf J CommRingCat.{max c v u})
    (F : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) ⥤
      SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj B))
    [hF : F.Additive]
    (η : ∀ (M : SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) (V : Cᵒᵖ),
      M.val.obj V → (F.obj M).val.obj V)
    (P Q : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, c, v} J B).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (hpq : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    (e.hom.f k).val.app V
      (η (((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)).X k) V
        (coefficientTensorGenerator.{u, c, v} J A P Q p q k hpq V x y)) =
      coefficientTensorGenerator.{u, c, v} J B
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q k hpq V
        (η (P.X p) V x) (η (Q.X q) V y)

/-- Forget scalar restriction on a section, keeping its underlying element. -/
def coefficientRestrictionSection
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {A B : Sheaf J RingCat.{r}} (φ : A ⟶ B) (M : SheafOfModules.{r} B) (V : Cᵒᵖ)
    (x : ((SheafOfModules.restrictScalars φ).obj M).val.obj V) : M.val.obj V := x

/-- The integral-to-finite adjunction unit on the underlying local section. -/
noncomputable def coefficientIntegralScalarUnitSection (n : ℕ)
    (M : scalarReductionSource l E W) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    ((scalarReductionExtension l E W n).obj M).val.obj V :=
  coefficientRestrictionSection
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    ((scalarReductionExtension l E W n).obj M) V
    (((coefficientOrdinaryScalarAdjunction l E W n).unit.app M).val.app V x)

attribute [local irreducible] coefficientActualScalarDerivedPair

/-- The ordinary finite scalar-extension tensor comparison is uniquely determined by its
unit formula on tensor generators, in every total-degree summand. -/
theorem coefficientScalarTensorIso_exists (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ∃! e : ((scalarReductionExtension l E W n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P,
           ((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q),
      CoefficientScalarTensorGenerators.{u, t+1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)
        (integralCoefficientCommRingSheaf l E W n) (scalarReductionExtension l E W n)
        (hF := coefficientFiniteExtensionAdditive l E W n)
        (coefficientIntegralScalarUnitSection l E W n) P Q e := by
  classical
  let J := Scheme.ProEt.topology W
  let a := completedIntegralCommRingProjectionUnrestricted l E W n
  let (R : Sheaf J CommRingCat.{max u (t+1)}) :
      HasDerivedCategory (SheafOfModules.scalarModules J R) := HasDerivedCategory.standard _
  obtain ⟨M⟩ := CategoryTheory.scalarHomModels_exists.{t+1, t, u,
    max (t+2) (u+1)} J
  let : (show SheafOfModules.scalarModules J
      (completedIntegralCommRingSheafUnrestricted l E W) ⥤
        SheafOfModules.scalarModules J (integralCoefficientCommRingSheaf l E W n)
      from scalarReductionExtension l E W n).Additive :=
    coefficientFiniteExtensionAdditive l E W n
  exact CategoryTheory.ScalarHomTensor.pairTensorIso_existsUnique_with_ordinary a
    (coefficientActualScalarDerivedPair l E W n) M
    (scalarReductionExtension l E W n)
    (coefficientOrdinaryScalarAdjunction l E W n)
    (coefficientActualScalarDerivedPair_extension l E W n)
    (coefficientActualScalarDerivedPair_ordinaryAdjunction_heq l E W n) P Q

/-- Selection from a unique characterization, given by `ExistsUnique.choose`. -/
noncomputable def coefficientUniqueComparisonChoice
    {α : Sort a} {p : α → Prop} (h : ∃! x, p x) : α := h.choose

attribute [local irreducible] coefficientUniqueComparisonChoice

/-- The unique ordinary scalar tensor comparison, with its generator normalization. -/
noncomputable def coefficientScalarTensorIso (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :=
  coefficientUniqueComparisonChoice (coefficientScalarTensorIso_exists l E W n P Q)

end StandardCoefficientInstances
end WeilConjectures
