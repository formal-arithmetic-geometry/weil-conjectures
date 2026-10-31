/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
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
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.ProperBaseChange.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.ProperBaseChange.KInjectiveHomComplexSupplement
import WeilConjectures.ProperBaseChange.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

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

/-- Integral pullback, completed tensor and internal Hom commute naturally with finite
scalar extension, compatibly with towers and the identity coefficient extension.
Source: Weil blueprint, `def-weil-derived-pullback-tensor-hom`, integral/common-stage
paragraph (blueprint: lem-pur-integral-operations-scalar-extension).

Proof:
1. For A = O_E and B = O_L, valuation compatibility gives t = u*v^e. Finite residue
quotients give a basis of B/tB over A/tA. Lift it and successively expand coefficients
in powers of t. Completeness gives spanning; dividing a nonzero relation by its
smallest valuation and reducing modulo t gives independence. Hence B is finite free,
with one basis compatible with every reduction [lem-weil-valued-dvr-finite-quotients,
lem-weil-l-adic-extension-complete, def-weil-l-adic-coefficient-extension].
2. Taking limits of these finite-level bases identifies S_W with R_W tensor_A B.
The v^(en) subsequence is cofinal. Finite sums commute with these limits, so S_W is
finite free over R_W. The two-term resolution of A/t^n identifies the completed-ring
quotient with the constant finite coefficient sheaf
[def-weil-completed-integral-coefficients,
lem-weil-pbc-completed-constant-sheaf-reduction].
3. The Koszul reflector is the strict quotient-tower completion C_R. Comparing its
Roos triangle with the defining completeness triangle first proves that a complete
input is locally complete and then that the canonical unit is invertible. Cofinal
compression of the strict tower is a natural chain homotopy equivalence: in each
block eliminate intermediate coordinates of 1-s by invertible triangular substitutions.
The discarded identity cones are contractible. All substitutions use finite sums and
preserve the augmentation [lem-weil-pbc-ringed-koszul-completion-reflector,
def-weil-derived-complete, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-proetale-countable-products-exact, def-weil-abstract-derived-category].
4. Ordinary finite free extension T commutes with products and cones, hence C_S T is
naturally T C_R. The integral scalar functor is C_S T, with the actual quotient maps
and zero shifted cone component. On complete objects its specified comparison with T
is invertible, and T preserves completeness [lem-pur-derived-change-of-rings,
def-weil-integral-scalar-extension]. The published completion chain and ordinary tensor
associator fix the auxiliary maps in Comparisons uniquely; their normalization is
precisely this comparison, including on nonconstructible complete outputs.
5. Resolve K by a flat-term K-flat complex P. Ambient pullback preserves K-flatness.
Both scalar/pullback routes are S_X tensor over f^(-1)R_Y with f^(-1)P. Associate their
ordinary tensors, then apply the completion comparison of step 4. Finite constant
inverse image is exact, so the quotient towers give exactly the recorded completed
pullbacks [lem-pc-kflat-resolution, def-pur-integral-derived-operations,
prop-weil-pbc-proetale-constant-exact,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
6. On two K-flat representatives, the finite-level tensor associator identifies the
quotient tower with the reductions of the ordinary ambient tensor. Ordinary scalar
extension commutes with this tensor. Step 4 then identifies the completed tensors
[def-pur-integral-derived-operations, lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
7. Internal Hom into a complete N is complete. On every slice, derived currying
identifies Hom(R[1/t], Hom(M,N)) with Hom(M, Hom(R[1/t],N)), which vanishes. The
complete-elements ideal criterion supplies the criterion for every element of (t).
The reflector then gives completeness and step 4 applies
[lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-weil-pbc-ringed-koszul-completion-reflector,
lem-weil-pbc-ringed-derived-complete-elements-ideal].
8. A K-injective S-resolution remains K-injective over R, because its left adjoint
is exact finite free tensor. This holds on every slice. The tensor/Hom adjunction
therefore identifies restricted Hom_S(T M,T N) with Hom_R(M,Res T N). In a temporary
basis T N is N^d; finite sums of K-injectives remain K-injective. Thus the canonical
map Hom_R(M,N) tensor S to Hom_R(M,N tensor S), h tensor s mapping m to h(m) tensor s,
is invertible. It is S-linear and independent of the basis
[def-pur-derived-internal-hom, prop-pur-kinjective-resolutions-exist,
lem-pur-kinjective-restrict-localized].
9. The maps are natural, since tensor universal maps, evaluation and strict cone
maps are natural. For a coefficient tower the scalar associator is multiplication:
(p tensor s) tensor s' maps to p tensor ss'. The pullback and tensor diagrams agree
on these generators. Uncurrying the Hom diagram makes both paths send (h,s,s',m,t')
to h(m) tensor ss't'. These equalities commute with differentials, quotients, products
and cones, hence descend. With E=L, scalar extension is completion; its unit is the
normalized quotient augmentation. The three unit diagrams then give identity under
this identification. Constructibility preservation is the stipulated published
scalar-extension result [lem-weil-integral-scalar-extension-constructible]; no finite
Tor amplitude, perfectness, or constructibility of the internal Hom is required. -/
theorem integralOperationsScalarExtension
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (X Y : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    IntegralScalarOperations.Comparisons l Ω X Y f := by
  sorry

end WeilConjectures
