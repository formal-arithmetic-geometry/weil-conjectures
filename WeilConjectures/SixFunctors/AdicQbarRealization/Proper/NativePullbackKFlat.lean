/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.Algebra.Homology.RingedSiteKFlatStalkCriterion
import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.RingedSitePointExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.RingedSitePointFinitePresentationRetract
import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import WeilConjectures.CategoryTheory.Sites.NormalizedFreeModuleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.Sites.FinitarySliceEnoughPoints
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.FinitarySiteEnoughPoints
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import WeilConjectures.CategoryTheory.Sites.PointSystemSaturation
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.PointSystemRefineAll
import WeilConjectures.CategoryTheory.PointSystemRefinementMap
import WeilConjectures.AlgebraicGeometry.PointSystemRefine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.PointSystemRefinementChainExists
import WeilConjectures.CategoryTheory.PointSystemChain
import Mathlib.Order.Directed
import WeilConjectures.CategoryTheory.PointSystemExtensions
import WeilConjectures.CategoryTheory.PointSystemDiagram
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Order.Hom.Set
import WeilConjectures.CategoryTheory.PointSystemPosetalRefine
import WeilConjectures.CategoryTheory.PointSystemPosetalReplacement
import Mathlib.Order.Antisymmetrization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.PointSystemSchedule
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.CategoryTheory.Filtered.Grothendieck
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Sites.PointFamilyConservative
import WeilConjectures.TraceFormula.InverseSystemSitePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-! # Native pullback preserves all K-flat complexes

Source: Stacks Tags 0DEN, 0DEP and 0G7E.
(blueprint: lem-sf-native-pullback-kflat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
attribute [local irreducible] proEtaleModuleInverseImage

set_option maxHeartbeats 4800000 in
-- The independent-coefficient stalk and scalar transports elaborate large site instances.
/-- Pullback of native modules preserves K-flatness without any termwise-flatness
hypothesis. Source: Stacks Tags 0DEN, 0DEP and 0G7E.
(blueprint: lem-sf-native-pullback-kflat).

Proof: use the algebraic presentation of pro-etale inverse image. At every point of
the source, its stalk is a stalk at the composite point of the target, so K-flatness
is preserved by the stalk criterion. The conservative family of pro-etale points
reflects this property on the source. Scalar extension then preserves K-flatness by
balanced tensor cancellation with exact restriction of scalars. The recorded object
and map equations identify that scalar extension with the actual native extension.
This proof covers all complexes, empty schemes and zero coefficient rings. -/
theorem nativePullbackKFlat {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage p).obj A ⟶ B)
    [(ContinuousRational.modulePull p c).Additive]
    (P : CochainComplex (pbcModules Y A) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := A) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := B)
      (((ContinuousRational.modulePull p c).mapHomologicalComplex (.up ℤ)).obj P) := by
  let I := modelNormalizedAlgebraicLift p A
  let g : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage p (Type (u + 1))
      direct := proEtaleSheafDirectImage p (Type (u + 1))
      adj := proEtaleSheafAdjunction p (Type (u + 1))
      leftExact :=
        (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage p (𝟙 Y)).2.2.2.1 }
  let I' := SheafOfModules.inverseImageOfUniverses I
  haveI : (T p A).Additive := by
    constructor
    intro M N f g
    ext V m
    rfl
  haveI : (proEtaleModuleInverseImage p A).Additive :=
    (canonicalAdjunction p A).left_adjoint_additive
  haveI : I'.modules.Additive :=
    (show (proEtaleModuleInverseImage p A).Additive from inferInstance)
  obtain ⟨ι, points, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint
      ((adicTowerInverseImage p).obj A) (points i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (points i))
  have hc : JointlyReflectIsomorphisms (fun i ↦ (points i).inverse) := by
    constructor
    intro M N f _
    exact hp f (fun i ↦ (isIso_iff_bijective ((points i).inverse.map f)).1 inferInstance)
  have hI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) g I' ι points s hc P hP
  let h := (completedAdicChangeData X c).choose_spec.choose
  have hm : ∀ {M N : pbcModules X ((adicTowerInverseImage p).obj A)} (f : M ⟶ N),
      (pbcExtend c).map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom c M f ≫
        eqToHom (h N).symm :=
    (completedAdicChangeData X c).choose_spec.choose_spec.choose
  have hE := SheafOfModules.changeOfRings_isKFlat_independentCoefficients c
    (((proEtaleModuleInverseImage p A).mapHomologicalComplex (.up ℤ)).obj P)
    (pbcExtend c) h hm hI
  exact hE

end WeilConjectures.AdicQbarRealization.Proper
