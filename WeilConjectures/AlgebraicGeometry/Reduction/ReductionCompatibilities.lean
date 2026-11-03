/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
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
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows

/-! # Units, composition and purity under finite coefficient change

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.md and its proof
(blueprint: det-sp-reduction-compatibilities).

The first two identities use the intrinsic constant-ring Dctf adjunctions. The third
uses the equivalent fixed-coefficient presentation of the general-ring purity node,
including its actual diagonal/Rees/integration normalization. No flatness is assumed.

## Main statements

* `reductionCompatibilities_unit`: coefficient change preserves the adjunction unit.
* `reductionCompatibilities_composition`: the exceptional comparisons satisfy the cocycle.
* `reductionCompatibilities_purity`: coefficient change preserves normalized smooth purity.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
open MonoidalCategory

-- The comparison-origin and tensor-naturality arguments are independent of
-- the finite-level purity assembly and its dimension-zero normalization.
private theorem compatibilityIntrinsicOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    ∃ K₀ : DerivedCategoryModule A T,
      DerivedCategory.boundedConstructibleFiniteTor A T K₀ ∧
      Nonempty ((comparison A T).obj K₀ ≅ K) := by
  obtain ⟨a, b, hab, hv⟩ := hK.2.1
  have hbd : _root_.DerivedCategory.TStructure.t.bounded K :=
    ⟨⟨a, (_root_.DerivedCategory.isGE_iff K a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
     ⟨b, (_root_.DerivedCategory.isLE_iff K b).mpr
      (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  have hc := ProEtale.exceptionalTransport_constructible_comparison A T
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := (congrFun hc K).mp ⟨hbd, hK.1⟩
  have hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K₀ := by
    obtain ⟨hc, a, b, _, hv⟩ := hK₀
    exact ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff K₀ a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff K₀ b).mpr
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩,
      fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
  refine ⟨K₀, ⟨hbc, ?_⟩, ⟨e⟩⟩
  obtain ⟨c, d, hcd, ht⟩ := hK.2.2
  refine ⟨c, d, ?_⟩
  apply (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d K₀).mp
  exact (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso e.symm ht

private theorem compatibilityIntrinsicOriginCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := compatibilityIntrinsicOrigin A T K hK
  let adj := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T
  have hp : _root_.DerivedCategory.TStructure.t.plus K₀ := hK₀.1.1.1
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀ hp
  have hu : IsIso ((comparison A T).map (adj.unit.app K₀)) := inferInstance
  have hc : IsIso (adj.counit.app ((comparison A T).obj K₀)) :=
    IsIso.of_isIso_fac_left (adj.left_triangle_components K₀)
  exact (NatTrans.isIso_app_iff_of_iso adj.counit e).mp hc

private theorem compatibilityActualOriginCtf
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) :
    DerivedCategory.boundedConstructibleFiniteTor A T ((origin A T).obj K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := compatibilityIntrinsicOrigin A T K hK
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat A) T K₀
    hK₀.1.1.1
  let q : K₀ ≅ (origin A T).obj K :=
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).unit.app K₀) ≪≫
      (origin A T).mapIso e
  exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso q hK₀.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso q hK₀.2⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalarOriginCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Y : Scheme.{u}) [IsNoetherian Y]
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat B) Y).counit.app
      ((proScalar φ Y).obj K)) := by
  let a := ProEtale.derivedComparisonAdjunction (ModuleCat A) Y
  let b := ProEtale.derivedComparisonAdjunction (ModuleCat B) Y
  have : IsIso (a.counit.app K) := compatibilityIntrinsicOriginCounit A Y K hK
  have hplus := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ Y
    ((origin A Y).obj K) (compatibilityActualOriginCtf A Y K hK).2
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) Y
    ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) hplus
  have : IsIso (b.counit.app ((comparison B Y).obj
      ((ordinaryScalar φ Y).obj ((origin A Y).obj K)))) :=
    IsIso.of_isIso_fac_left (b.left_triangle_components _)
  let e : (comparison B Y).obj ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) ≅
      (proScalar φ Y).obj K :=
    ((ProEtale.pbcComparisonReduction Y φ).app ((origin A Y).obj K)).symm ≪≫
      (proScalar φ Y).mapIso (asIso (a.counit.app K))
  exact (NatTrans.isIso_app_iff_of_iso b.counit e).mp inferInstance

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
