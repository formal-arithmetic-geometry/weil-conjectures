/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Ring.Adjunctions
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary realization of coefficient-sized constant module sheaves

Source: Stacks Project, Tags 03CY and 09AL; coefficient transport in the opening
paragraph of the finite comparison proof
(blueprint: lem-ctf-finite-comparison-model-realization).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section ConstantScalars
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A]

private instance commRingForgetSheafification :
    J.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) where
  le := by
    intro P Q f hf
    let : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
    let : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
    let : Presheaf.IsLocallyInjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    let : Presheaf.IsLocallySurjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f
      (forget₂ CommRingCat.{u} RingCat.{u}))

private def coefficientRingIso : SheafOfModules.constantCoefficientRing J A ≅
    (constantSheaf J RingCat.{u}).obj (RingCat.of A) :=
  (constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).app (CommRingCat.of A)

private def ringRestriction : ConstantCompletion.Mod (ConstantCompletion.constant J A) ⥤
    SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of A)) :=
  SheafOfModules.restrictScalars (coefficientRingIso J A).inv

private theorem coefficientRingIso_unit :
    SheafOfModules.constantCoefficientUnit J A ≫ (coefficientRingIso J A).hom.hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A)) := by
  change SheafOfModules.constantCoefficientUnit J A ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).hom.app
      (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  unfold SheafOfModules.constantCoefficientUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u} RingCat.{u})).hom).symm.trans
      (by rfl)

private theorem restriction_smul (M : ConstantCompletion.Mod (ConstantCompletion.constant J A))
    (V : Cᵒᵖ) (a : A) (x : M.val.obj V) :
    a • (show ((ringRestriction J A ⋙ constantRingModuleRestriction J A).obj M).obj.obj V
      from x) =
    a • (show ((coefficientModelFixedScalars J A).obj M).obj.obj V from x) := by
  have h := congrArg (fun f ↦ f.app V a) (coefficientRingIso_unit J A)
  have hi := congrArg (fun f ↦ f.hom.app V) (coefficientRingIso J A).hom_inv_id
  change (coefficientRingIso J A).inv.hom.app V
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app V a) • x =
      (SheafOfModules.constantCoefficientUnit J A).app V a • x
  erw [← h]
  exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)

end ConstantScalars
end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

end AlgebraicGeometry.ProEtale
