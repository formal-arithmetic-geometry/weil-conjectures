/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Topology.ProfiniteCondensedRing
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
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
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
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
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Adjunction.Mates
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Realization of finite normed coefficient fields

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.8.1 and
Remark 6.8.15; the node's algebraic embedding and scalar transport expansion
(blueprint: lem-sfb-normed-coefficient-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormedCoefficientRealization

/-- The actual termwise inverse scalar restriction for the point-induced coefficient
isomorphism. Source: the node's proof step 4; Stacks 03CZ
(blueprint: lem-sfb-normed-coefficient-realization). -/
abbrev transport {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') (Z : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ'.X Z)) :=
  (Mod.comap (coefficientMap a.inv.hom Z) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ'.X Z)).mapDerivedCategory

private local instance comap_iso_equivalence {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.comap φ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R).IsEquivalence :=
  (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor

end AlgebraicGeometry.ProEtale.NormedCoefficientRealization
