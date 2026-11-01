/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
public import WeilConjectures.AlgebraicGeometry.ClosedFiniteTransport.ClosedFiniteAdjointCounitTransport
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemQuotientNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalDerivedSiteRealization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteSupportRealization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CurveOpenDirectImage
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.ConstructibleSheaf.ExtensionByZero
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Support.SupportLocalizationTriangle
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleClosedProjection.ProEtaleClosedUnderivedProjection
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedTensorProjection
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit

/-! # Counit normalization of the closed exceptional functor

Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, exceptional identification in (2)--(3).
(blueprint: lem-sf-finite-exceptional-site-normalization).

Finite sheaves are written in the existing fixed-module coordinates. The predicate
below uses the canonical intrinsic realization, so its domain is precisely D^b_c,
without a finite-Tor condition. Adjunctions are quantified as presentations of the
kernel adjoint: their normalized comparison is determined by their counit.
Natural-number levels denote positive exponents n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptionalNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded positive quotient, lifted to the small site's value universe.
Source: blueprint localization, finite stage
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev A (n : ℕ) := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

/-- The fixed-module presentation of the original small pro-etale derived category.
Source: blueprint localization, finite stage
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev C (T : Scheme.{u}) (n : ℕ) :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (A l E n)))

/-- Bounded constructibility, tested through the canonical intrinsic realization.
Source: blueprint localization, K in D^b_c(X,A_n)
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def bc (T : Scheme.{u}) (n : ℕ) : ObjectProperty (C l E T n) :=
  fun K ↦ intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T
    ((ProEtale.finiteCoefficientIntrinsicRealization T
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj K)

/-- The actual etale compact-support functor at (id_Z,i).
Source: blueprint localization, finite exceptional adjoint
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev etaleSupport {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (A l E n))
    (Compactification.ofIsProper i)

/-- The same ordinary etale right adjoint as in the specified exceptional definition.
Source: blueprint localization, finite exceptional adjoint
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev etaleExceptional {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  (etaleSupport l E i n).rightAdjoint

/-- The literal comparison-site formula at the specified compactification.
Source: blueprint localization, displayed finite identification
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev exceptional {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  ProEtale.sfFiniteExceptionalAt (A l E n) (Compactification.ofIsProper i)

/-- The ordinary unbounded closed direct image in the same coordinates.
Source: blueprint localization, ambient kernel adjunction
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev image {X Z : Scheme.{u}} (i : Z ⟶ X) (n : ℕ) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (A l E n)) i).rightDerivedFunctor

/-- The specified transported exceptional counit, with closed direct image expressed
as its right-derived functor. The exact termwise comparison is canonical.
Source: blueprint localization, finite counit normalization
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def counit {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : IsCompl (Set.range i) (Set.range j)) (n : ℕ) (K : C l E X n) :
    (image l E i n).obj ((exceptional l E i n).obj K) ⟶ K :=
  haveI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl
    (R := A l E n) i j h
  (Functor.rightDerivedFunctorIsoMapDerivedCategory
    (ProEtale.lowerStar (ModuleCat.{u + 1} (A l E n)) i)).hom.app _ ≫
    ProEtale.ClosedFiniteTransport.transportedCounit (A l E n) i j h K

/-- Actual positive quotient, induced by the identity on the valuation ring.
Source: blueprint localization, coefficient quotients
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def quotient {m n : ℕ} (h : n ≤ m) : A l E m →+* A l E n :=
  (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).ulift

/-- The actual finite scalar extension, without a flatness hypothesis.
Source: blueprint localization, derived reduction
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev scalar (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  ProEtale.pbcFixedScalarExtension (ProEt.topology T) (quotient l E h)

/-- Exact comparison inverse image in the recorded fixed-module coordinates.
Source: blueprint localization, etale origins
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev site (T : Scheme.{u}) (n : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A l E n)) T).mapDerivedCategory

/-- The origin map is the image of the actual comparison-adjunction unit.
Source: blueprint localization, origin independence
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def origin {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (P : Etale.DerivedCategoryModule (A l E n) X) :
    (site l E Z n).obj ((etaleExceptional l E i n).obj P) ⟶
      (exceptional l E i n).obj ((site l E X n).obj P) :=
  (site l E Z n).map ((etaleExceptional l E i n).map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} (A l E n)) X).unit.app P))

/-- The kernel quotient map is literally the mate of inverse closed projection.
Source: blueprint localization, coefficient-extended exceptional counit
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def quotientMate {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : ∀ n : ℕ, C l E X n ⥤ C l E Z n)
    (a : ∀ n : ℕ, image l E i n ⊣ J n) {m n : ℕ} (h : n ≤ m)
    (q : image l E i m ⋙ scalar l E X h ≅ scalar l E Z h ⋙ image l E i n) :
    J m ⋙ scalar l E Z h ⟶ scalar l E X h ⋙ J n :=
  (mateEquiv (a m) (a n) (TwoSquare.mk _ _ _ _ q.inv)).natTrans

/-- Quotient compatibility with the ordinary etale counit transpose. The equation is
in the smaller coefficient category and therefore retains its complete scalar action.
Its source ranges over all constructible origins, and naturality gives the same equation
for every isomorphic pro-etale input. Only the stated boundedness of its reduction is used.
Source: blueprint localization, finite quotient normalization
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
structure Quotients {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i) (Set.range j))
    (J : ∀ n : ℕ, C l E X n ⥤ C l E Z n)
    (a : ∀ n : ℕ, image l E i n ⊣ J n)
    (N : ∀ n : ℕ, FiniteNormalization l E i j hij n (J n) (a n)) where
  projection {m n : ℕ} (h : n ≤ m) :
    image l E i m ⋙ scalar l E X h ≅ scalar l E Z h ⋙ image l E i n
  projection_eq {m n : ℕ} (h : n ≤ m) (P : C l E Z m) :
    (projection h).hom.app P =
      ProEtale.finiteCoefficientChangeDirectImageMap (quotient l E h) i P
  etaleProjection {m n : ℕ} (h : n ≤ m) :
    etaleSupport l E i m ⋙ Etale.scalarExtension (quotient l E h) X ≅
      Etale.scalarExtension (quotient l E h) Z ⋙ etaleSupport l E i n
  etaleProjection_eq {m n : ℕ} (h : n ≤ m) :
    (etaleProjection h).hom =
      Etale.compactScalarMap (quotient l E h) (Compactification.ofIsProper i)
  origins (n : ℕ) (P : Etale.DerivedCategoryModule (A l E n) X)
      (hP : Etale.DerivedCategory.isBoundedConstructible (A l E n) X P) :
    IsIso (origin l E i n P)
  compatible {m n : ℕ} (h : n ≤ m)
      (P : Etale.DerivedCategoryModule (A l E m) X)
      (hP : Etale.DerivedCategory.isBoundedConstructible (A l E m) X P)
      (hC : bc l E X m ((site l E X m).obj P))
      (hD : bc l E X n ((site l E X n).obj
        ((Etale.scalarExtension (quotient l E h) X).obj P))) :
    (scalar l E Z h).map (origin l E i m P) ≫
        (scalar l E Z h).map ((N m).comparison.inv.app ⟨_, hC⟩) ≫
        (quotientMate l E i J a h (projection h)).app ((site l E X m).obj P) ≫
        (J n).map ((ProEtale.pbcComparisonReduction X (quotient l E h)).hom.app P) =
      (ProEtale.pbcComparisonReduction Z (quotient l E h)).hom.app
          ((etaleExceptional l E i m).obj P) ≫
        (site l E Z n).map
          ((Etale.etaleCoefficientQuotientMate (quotient l E h)
            (Compactification.ofIsProper i)
            (Adjunction.ofIsLeftAdjoint (etaleSupport l E i m))
            (Adjunction.ofIsLeftAdjoint (etaleSupport l E i n))
            (etaleProjection h)).app P) ≫
        origin l E i n ((Etale.scalarExtension (quotient l E h) X).obj P) ≫
        (N n).comparison.inv.app ⟨_, hD⟩

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]

end WeilConjectures.FiniteExceptionalNormalization
