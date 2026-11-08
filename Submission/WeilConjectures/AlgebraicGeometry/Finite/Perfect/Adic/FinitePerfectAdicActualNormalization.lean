/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import Submission.WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Submission.WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Submission.WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Submission.WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import Submission.WeilConjectures.AlgebraicGeometry.Source.SourceIsomorphismNormalizedPresheafEvaluation
import Submission.WeilConjectures.CategoryTheory.Constant.ConstantDerivedNormalizationUniversalSupplement
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualRealization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The actual-quotient half of a finite perfect normalization diagram

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Descent and scalar comparisons for the actual quotient tower, against the explicit
constant diagram. This data has no Isom-presheaf reduction maps or constant-model
boundedness, lisse, or universality assertions.
Source: Stacks Tags 09AL and 09C6, finite quotient descent and balancing.
(blueprint: def-weil-pbc-finite-perfect-adic-actual-normalization). -/
structure FinitePerfectAdicActualNormalization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) where
  K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  boundedK : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  lisseK : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  stalk : ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ V.left), Nonempty
      ((pointSmallEtale x).sheafFiber.obj
        (derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) (K n)))
  dK : ∀ n : ℕ, K (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n)
  universalK : ∀ n : ℕ, EtaleUniversalNormalization V.left
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)
  realization : ∀ (U : V.left.ProEt) (W : X.ProEt),
    (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W))
  scalar : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    normalizationRestrict (ProEt.topology U.left)
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ⋙
          realization U W f (n + 1) ≅
      realization U W f n
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
  model_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op

end AlgebraicGeometry.Scheme
