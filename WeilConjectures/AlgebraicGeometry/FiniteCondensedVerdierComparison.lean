/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Finite condensed Verdier comparison

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i)
(blueprint: lem-sf-finite-condensed-verdier-comparison).
The statement uses actual module objects and records the compact-support counit
normalization and the evaluation transpose, without any double-dual assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u v w v₀ w₀ c d c₀ d₀
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- The inverse-image mate of the normalized direct-image section identity.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingPullbackIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙
        (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅
      EU.functor ⋙ R := encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- The open-extension mate of the normalized restriction comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingOpenShriekIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := finiteCondensedEncodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- The canonical derived direct-image encoding comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingDerivedPushforwardIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- The canonical derived open-extension encoding comparison.
Source: latest blueprint, coefficient comparison paragraph (i), using the normalized
section-action comparison and uniqueness of adjoints
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedEncodingDerivedOpenShriekIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (finiteCondensedEncodingOpenShriekIso A j eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso EU.functor G

/-- The canonical support comparison: the normalized section-action proper and open
comparisons, conjugated by the inverse encodings, followed by the ordinary site map.
It is defined on bounded-below complexes; only its constructible restriction is used.
Source: latest blueprint, paragraph (i), compatibility with compact support
(blueprint: lem-sf-finite-condensed-verdier-comparison). -/
def finiteCondensedSupportComparison
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    {T S : Scheme.{u}} {a : T ⟶ S} (c : Compactification a)
    (eT : Encoding A T) (eS : Encoding A S) (eZ : Encoding A c.Z) :
    _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⋙ internalEtaleRealization A S eS ≅
      _root_.DerivedCategory.Plus.ι ⋙ internalEtaleRealization A T eT ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c := by
  let d : CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
      eS.fixedDerived.functor ≅ eT.fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (finiteCondensedEncodingDerivedPushforwardIso A c.g eS eZ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (finiteCondensedEncodingDerivedOpenShriekIso A c.i eZ eT) _ ≪≫
      Functor.associator _ _ _
  let di := Iso.inverseCompIso (G := eT.fixedDerived)
    (Iso.isoCompInverse (H := eS.fixedDerived) d ≪≫ Functor.associator _ _ _)
  let j := (compactSupportSiteComparison (ULift.{u + 1} A) c).symm
  exact Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
      (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight j eS.fixedDerived.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι
      (Functor.isoWhiskerLeft
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory
        di.symm) ≪≫
    Functor.isoWhiskerLeft _root_.DerivedCategory.Plus.ι (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary


namespace Padic

end Padic

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary


end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
