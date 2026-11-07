/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import Submission.WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import Submission.WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import Submission.WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import Submission.WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import Submission.WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.LeftExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.RingTheory.Ideal.Span
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Submission.WeilConjectures.Algebra.Homology.HomTensorTotal
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import Submission.WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Submission.WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Submission.WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Integral operations and finite coefficient extension

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations,
`def-weil-derived-pullback-tensor-hom`, integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension).

The comparison predicate records all three natural isomorphisms and their actual
composition and identity diagrams. Scalar associators are normalized by the published
ordinary tensor associator and the published strict quotient-completion chain map.
This normalization also applies to complete internal Homs that are not constructible.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory Opposite

namespace WeilConjectures.IntegralScalarOperations

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]

/-- An abbreviation for the recorded ambient completed-coefficient category.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
abbrev Ambient (E : Padic.FiniteCoefficientFields l Ω) (W : AlgebraicGeometry.Scheme.{u}) :=
  DerivedCategory (integralTowerModules.{u, u} l E.val W)

/-- The recorded completed scalar functor for the actual intermediate-field inclusion.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
noncomputable abbrev extend {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (W : AlgebraicGeometry.Scheme.{u}) :=
  integralScalarExtension l E.val L.val (IntermediateField.inclusion h) W

/-- The published exact ordinary finite-free scalar model.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
noncomputable abbrev ordinary {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (W : AlgebraicGeometry.Scheme.{u}) :=
  integralOrdinaryDerivedScalar l E.val L.val (IntermediateField.inclusion h) W

/-- The recorded intrinsic bounded constructible predicate, with no finite-field datum.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
noncomputable abbrev constructible (E : Padic.FiniteCoefficientFields l Ω)
    (W : AlgebraicGeometry.Scheme.{u}) := sfIntegralConstructible l E.val W

/-- The recorded derived-complete predicate, also for nonconstructible outputs.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
noncomputable abbrev complete (E : Padic.FiniteCoefficientFields l Ω)
    (W : AlgebraicGeometry.Scheme.{u}) := IsSfDerivedComplete l E.val W

/-- The two schemes occurring in the statement; false selects Y and true selects X.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def site (X Y : AlgebraicGeometry.Scheme.{u}) (w : Bool) := if w then X else Y

/-- Exactly the three comparison families, with naturality, scalar-composition
compatibility and identity normalization. The auxiliary scalar maps are fixed by their
quotient-completion comparison and ordinary tensor multiplication, rather than supplied
as arbitrary comparison isomorphisms. The site flag ranges over precisely X and Y.
Source: blueprint integral/common-stage paragraph
(blueprint: lem-pur-integral-operations-scalar-extension). -/
noncomputable def Comparisons (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y) : Prop :=
  ∃ (completion : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool),
    ordinary l Ω h (site X Y w) ⟶ extend l Ω h (site X Y w)),
  ∃ (preserves_constructible : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (w : Bool) (K : Ambient l Ω E (site X Y w)), constructible l Ω E (site X Y w) K →
      constructible l Ω L (site X Y w) ((extend l Ω h (site X Y w)).obj K)),
  ∃ (scalarComp : ∀ (E L F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ F)
    (w : Bool), extend l Ω h (site X Y w) ⋙ extend l Ω k (site X Y w) ≅
      extend l Ω (h.trans k) (site X Y w)),
  ∃ (scalarUnit : ∀ (E : Padic.FiniteCoefficientFields l Ω) (w : Bool),
    𝟭 (Ambient l Ω E (site X Y w)) ⟶ extend l Ω (le_refl E) (site X Y w)),
  ∃ (pullback : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (K : Ambient l Ω E Y), constructible l Ω E Y K →
      ((extend l Ω h X).obj ((integralDerivedPullback l E.val f).obj K) ≅
        (integralDerivedPullback l L.val f).obj ((extend l Ω h Y).obj K))),
  ∃ (tensor : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (M N : Ambient l Ω E (site X Y w)),
    constructible l Ω E (site X Y w) M → constructible l Ω E (site X Y w) N →
      ((extend l Ω h (site X Y w)).obj
          ((integralCompletedTensor l E.val (site X Y w)).obj (M, N)) ≅
        (integralCompletedTensor l L.val (site X Y w)).obj
          ((extend l Ω h (site X Y w)).obj M, (extend l Ω h (site X Y w)).obj N))),
  ∃ (hom : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (M N : Ambient l Ω E (site X Y w)),
    constructible l Ω E (site X Y w) M → constructible l Ω E (site X Y w) N →
      ((extend l Ω h (site X Y w)).obj
          ((integralDerivedInternalHom l E.val (site X Y w)).obj (op M, N)) ≅
        (integralDerivedInternalHom l L.val (site X Y w)).obj
          (op ((extend l Ω h (site X Y w)).obj M), (extend l Ω h (site X Y w)).obj N))),
  -- completion_normalization
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (w : Bool) (P : (integralOperationsGoodComplex l E.val (site X Y w)).FullSubcategory),
    (completion E L h w).app (DerivedCategory.Q.obj P.obj) ≫
        (integralScalarExtensionComparison l E.val L.val (IntermediateField.inclusion h)
          (site X Y w)).hom.app P =
      (integralOrdinaryScalar l E.val L.val (IntermediateField.inclusion h)
        (site X Y w)).mapDerivedCategoryFactors.hom.app P.obj ≫
      DerivedCategory.Q.map ((integralScalarCompletionChain l E.val L.val
        (IntermediateField.inclusion h) (site X Y w)).app P.obj)) ∧
  -- completion_isIso
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (K : Ambient l Ω E (site X Y w)), complete l Ω E (site X Y w) K →
      IsIso ((completion E L h w).app K)) ∧
  -- preserves_complete
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (K : Ambient l Ω E (site X Y w)), complete l Ω E (site X Y w) K →
      complete l Ω L (site X Y w) ((extend l Ω h (site X Y w)).obj K)) ∧
  -- scalarComp_normalization
  (∀ (E L F : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ F) (w : Bool) (K : Ambient l Ω E (site X Y w)),
    (ordinary l Ω k (site X Y w)).map ((completion E L h w).app K) ≫
        (completion L F k w).app ((extend l Ω h (site X Y w)).obj K) ≫
        (scalarComp E L F h k w).hom.app K =
      (integralOrdinaryDerivedScalarComp l E.val L.val (IntermediateField.inclusion h)
        (site X Y w) F.val (IntermediateField.inclusion k)).hom.app K ≫
        (completion E F (h.trans k) w).app K) ∧
  -- scalarUnit_normalization
  (∀ (E : Padic.FiniteCoefficientFields l Ω) (w : Bool),
    scalarUnit E w =
      (integralOrdinaryDerivedScalarUnit l E.val (site X Y w)).inv ≫
        completion E E (le_refl E) w) ∧
  -- hom_complete
  (∀ (E : Padic.FiniteCoefficientFields l Ω) (w : Bool)
    (M N : Ambient l Ω E (site X Y w)),
    constructible l Ω E (site X Y w) M → constructible l Ω E (site X Y w) N →
      complete l Ω E (site X Y w)
        ((integralDerivedInternalHom l E.val (site X Y w)).obj (op M, N))) ∧
  -- pullback_naturality
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (K K' : Ambient l Ω E Y) (hK : constructible l Ω E Y K)
    (hK' : constructible l Ω E Y K') (a : K ⟶ K'),
    (extend l Ω h X).map ((integralDerivedPullback l E.val f).map a) ≫
        (pullback E L h K' hK').hom =
      (pullback E L h K hK).hom ≫
        (integralDerivedPullback l L.val f).map ((extend l Ω h Y).map a)) ∧
  -- tensor_naturality
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (M N M' N' : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N)
    (hM' : constructible l Ω E (site X Y w) M')
    (hN' : constructible l Ω E (site X Y w) N') (a : M ⟶ M') (b : N ⟶ N'),
    (extend l Ω h (site X Y w)).map
        ((integralCompletedTensor l E.val (site X Y w)).map (Prod.mkHom a b)) ≫
        (tensor E L h w M' N' hM' hN').hom =
      (tensor E L h w M N hM hN).hom ≫
        (integralCompletedTensor l L.val (site X Y w)).map
          (Prod.mkHom ((extend l Ω h (site X Y w)).map a)
            ((extend l Ω h (site X Y w)).map b))) ∧
  -- hom_naturality
  (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (w : Bool)
    (M N M' N' : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N)
    (hM' : constructible l Ω E (site X Y w) M')
    (hN' : constructible l Ω E (site X Y w) N') (a : M' ⟶ M) (b : N ⟶ N'),
    (extend l Ω h (site X Y w)).map
        ((integralDerivedInternalHom l E.val (site X Y w)).map (Prod.mkHom a.op b)) ≫
        (hom E L h w M' N' hM' hN').hom =
      (hom E L h w M N hM hN).hom ≫
        (integralDerivedInternalHom l L.val (site X Y w)).map
          (Prod.mkHom (((extend l Ω h (site X Y w)).map a).op)
            ((extend l Ω h (site X Y w)).map b))) ∧
  -- pullback_comp
  (∀ (E L F : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ F) (K : Ambient l Ω E Y) (hK : constructible l Ω E Y K),
    (extend l Ω k X).map (pullback E L h K hK).hom ≫
        (pullback L F k ((extend l Ω h Y).obj K)
          (preserves_constructible E L h false K hK)).hom ≫
        (integralDerivedPullback l F.val f).map ((scalarComp E L F h k false).hom.app K) =
      (scalarComp E L F h k true).hom.app ((integralDerivedPullback l E.val f).obj K) ≫
        (pullback E F (h.trans k) K hK).hom) ∧
  -- tensor_comp
  (∀ (E L F : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ F) (w : Bool) (M N : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N),
    (extend l Ω k (site X Y w)).map (tensor E L h w M N hM hN).hom ≫
        (tensor L F k w ((extend l Ω h (site X Y w)).obj M)
          ((extend l Ω h (site X Y w)).obj N)
          (preserves_constructible E L h w M hM)
          (preserves_constructible E L h w N hN)).hom ≫
        (integralCompletedTensor l F.val (site X Y w)).map
          (Prod.mkHom ((scalarComp E L F h k w).hom.app M)
            ((scalarComp E L F h k w).hom.app N)) =
      (scalarComp E L F h k w).hom.app
          ((integralCompletedTensor l E.val (site X Y w)).obj (M, N)) ≫
        (tensor E F (h.trans k) w M N hM hN).hom) ∧
  -- hom_comp
  (∀ (E L F : Padic.FiniteCoefficientFields l Ω)
    (h : E ≤ L) (k : L ≤ F) (w : Bool) (M N : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N),
    (extend l Ω k (site X Y w)).map (hom E L h w M N hM hN).hom ≫
        (hom L F k w ((extend l Ω h (site X Y w)).obj M)
          ((extend l Ω h (site X Y w)).obj N)
          (preserves_constructible E L h w M hM)
          (preserves_constructible E L h w N hN)).hom ≫
        (integralDerivedInternalHom l F.val (site X Y w)).map
          (Prod.mkHom (((scalarComp E L F h k w).inv.app M).op)
            ((scalarComp E L F h k w).hom.app N)) =
      (scalarComp E L F h k w).hom.app
          ((integralDerivedInternalHom l E.val (site X Y w)).obj (op M, N)) ≫
        (hom E F (h.trans k) w M N hM hN).hom) ∧
  -- pullback_unit
  (∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : Ambient l Ω E Y) (hK : constructible l Ω E Y K),
    (scalarUnit E true).app ((integralDerivedPullback l E.val f).obj K) ≫
        (pullback E E (le_refl E) K hK).hom =
      (integralDerivedPullback l E.val f).map ((scalarUnit E false).app K)) ∧
  -- tensor_unit
  (∀ (E : Padic.FiniteCoefficientFields l Ω) (w : Bool)
    (M N : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N),
    (scalarUnit E w).app ((integralCompletedTensor l E.val (site X Y w)).obj (M, N)) ≫
        (tensor E E (le_refl E) w M N hM hN).hom =
      (integralCompletedTensor l E.val (site X Y w)).map
        (Prod.mkHom ((scalarUnit E w).app M) ((scalarUnit E w).app N))) ∧
  -- hom_unit
  (∀ (E : Padic.FiniteCoefficientFields l Ω) (w : Bool)
    (M N : Ambient l Ω E (site X Y w))
    (hM : constructible l Ω E (site X Y w) M)
    (hN : constructible l Ω E (site X Y w) N),
    (integralDerivedInternalHom l E.val (site X Y w)).map
        (Prod.mkHom (((scalarUnit E w).app M).op) (𝟙 N)) ≫
        (scalarUnit E w).app ((integralDerivedInternalHom l E.val (site X Y w)).obj (op M, N)) ≫
        (hom E E (le_refl E) w M N hM hN).hom =
      (integralDerivedInternalHom l E.val (site X Y w)).map
        (Prod.mkHom (𝟙 (op ((extend l Ω (le_refl E) (site X Y w)).obj M)))
          ((scalarUnit E w).app N)))

end WeilConjectures.IntegralScalarOperations

namespace WeilConjectures

end WeilConjectures
