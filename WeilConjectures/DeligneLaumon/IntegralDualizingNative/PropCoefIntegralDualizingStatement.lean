/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison

/-! # The integral dualizing object in the native condensed category

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/
prop-coef-integral-dualizing.md and prop-coef-integral-dualizing.proof.md.
(blueprint: prop-coef-integral-dualizing).

All integral coefficients below are the continuous condensed valuation ring pulled back
from the point. No category of completed coefficient systems is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures
namespace IntegralDualizingNative

/-- The coefficient unit, in the actual bounded constructible category. Membership is
provided by the existing rank-one coefficient-unit theorem.
Source: prop-coef-integral-dualizing, definition of omega
(blueprint: prop-coef-integral-dualizing). -/
def unit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] : ConstantModelBoundedConstructible Λ T :=
  ⟨𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj Λ T))), (condensedCoefficientUnit_mem Λ T).1⟩

/-- The same unit in the finite-Tor subcategory, without a new coefficient model.
Source: the finite exceptional value in prop-coef-integral-dualizing
(blueprint: prop-coef-integral-dualizing). -/
def finiteUnit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] : ConstantModelConstructibleFiniteTor Λ T :=
  ⟨(unit Λ T).obj, condensedCoefficientUnit_mem Λ T⟩

/-- Uniform reduction Tor interval, using the existing Tor-amplitude predicate and
ordinary derived scalar reduction at every positive coefficient level.
Source: prop-coef-integral-dualizing, uniform reduction Tor interval
(blueprint: prop-coef-integral-dualizing). -/
def reductionTorInterval (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (a b : ℤ) (K : DerivedCategory (AdicCompletion.Modules l E T)) : Prop :=
  ∀ (n : ℕ), DerivedCategory.torAmplitudeIn
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (AdicCompletion.finiteRing l E T n)) a b
        ((AdicCompletion.derivedReduction l E T n).obj K)

end IntegralDualizingNative

set_option maxHeartbeats 2000000 in
-- The statement elaborates several dependent derived scalar-change interfaces.
/-- The integral dualizing object is the exceptional inverse image of R[0], with its
canonical finite reductions, canonical completion map, uniform reduction Tor interval,
and natural adjunction of derived mapping complexes.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/
prop-coef-integral-dualizing.md; proof in the adjacent .proof.md, both paragraphs.
(blueprint: prop-coef-integral-dualizing).

Proof:
1. The continuous condensed O_E is an admissible non-finite coefficient and its positive
   quotients are admissible finite coefficients. The fixed algebraic closure has ell
   cohomological dimension zero; finite type makes X noetherian. For integral coefficients
   bounded constructible equals bounded constructible finite-Tor. Brown representability
   and constructible preservation restrict the compact-support right adjoint. Its value
   at the actual coefficient unit is omega in the displayed bounded constructible category.
2. Finite Verdier preservation takes the finite coefficient unit, of Tor interval [0,0],
   to the interval [-2d,0]. Finite duality site comparison and exact-interval Tor comparison
   preserve this interval, uniformly in the positive coefficient level.
3. The finite module equivalence identifies compact support with ordinary Rp_*j_!.
   Every finite-Tor test object has etale origin, and the transported exceptional functor
   preserves that class. Its class adjunction therefore represents the Brown Hom functor.
   Representing-object uniqueness identifies the two exceptional unit values, preserving
   the counit. Thus the finite omega values below are the finite dualizing objects.
4. For finite scalar change, the section equivalences preserve geometric and scalar
   adjunctions, their units and counits. The proper mate and open tensor normalizations
   identify the ordinary scalar comparison with the transported exceptional comparison:
   their adjuncts agree after precomposing the scalar-extension unit, so they agree.
5. Apply scalar-six to the listed maps R to A_(n+1) and A_(n+2) to A_(n+1).
   The compact-support scalar comparison is invertible. Its inverse followed by scalar
   extension of the counit and the regular-unit identification has a unique exceptional
   transpose. This gives the reduction isomorphisms. For successive quotients, paste the
   proper scalar-mate square with the open tensor square on bounded flat representatives.
   Proper-mate normalization and naturality identify this paste with the finite etale
   scalar comparison. The finite counit identity then identifies the two transposes.
   Scalar composition and the finite cocycle give precisely the two counit equations
   below, so the reduction comparisons identify the prescribed finite towers.
6. The integral criterion makes omega derived complete. For a K-flat representative the
   specified Roos augmentation is invertible. Strict scalar realization identifies its
   levels, units, and transitions with the canonical derived reduction tower. Conjugate
   by the normalized finite comparisons from step 5 to obtain the displayed derived
   limit of the finite exceptional values, through this canonical completion map.
7. Apply compact support to global derived mapping complexes and postcompose with the
   counit at R[0]. Exact point sections and the perfect-point equivalence identify the
   result with derived coefficient Hom into R[0]. This defines a natural map in D(R).
8. On degree-i cohomology this map is h mapped to epsilon[i] composed with Ra_!(h),
   which is the shifted adjunction bijection. Point evaluation is fully faithful on
   the constructible finite-Tor objects in question, so the map is a quasi-isomorphism.
9. Closed Hom is an exact right adjoint, and derived sections preserve derived limits.
   Scalar extension/restriction and step 6 express the source as the limit of finite
   derived Hom complexes. The integral criterion bounds the reductions of every K.
   Compact-support reduction and completeness of R similarly express the target as the
   limit of the finite coefficient derived Hom complexes.
10. Finite etale internal adjunction, finite duality site comparison, compact-support
    site comparison, the finite module equivalence and the site unit identify the middle
    finite maps with class-adjunction counit maps. Steps 3--5 identify their counits and
    reductions with the map of step 7. Their limit therefore agrees with that map. This
    gives the natural isomorphism of full derived mapping-complex functors below.
-/
theorem prop_coef_integral_dualizing_native
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ (d : WithBot ℕ∞)) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    letI : Fact (ringChar D.k).Prime :=
      ⟨(Algebra.ringChar_eq D.k₀ D.k) ▸ CharP.char_is_prime D.k₀ (ringChar D.k₀)⟩
    letI : Fact (ringChar D.k ≠ l) :=
      ⟨by
        let : Fintype D.k₀ := Fintype.ofFinite D.k₀
        let : Fact D.p.Prime := ⟨D.prime⟩
        have hc : Fintype.card D.k₀ = D.p ^ D.a := by
          simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
        let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
        let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
        rw [ringChar.eq D.k D.p]
        exact hl.symm⟩
    let R := DerivedNakayama.integerRing l E
    let A := fun n ↦ DerivedNakayama.quotientRing l E (n + 1)
    let s := Spec (.of D.k)
    letI : LocallyOfFiniteType (Over.mk (𝟙 s)).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 s))
    letI : QuasiCompact (Over.mk (𝟙 s)).hom := inferInstanceAs (QuasiCompact (𝟙 s))
    letI : IsSeparated (Over.mk (𝟙 s)).hom := inferInstanceAs (IsSeparated (𝟙 s))
    let f : X ⟶ Over.mk (𝟙 s) := Over.homMk X.hom
    let c := compactificationOverField f
    ∃ (hR : IsNativeExceptionalCoefficient l R)
      (hA : ∀ n, IsLocalizingAdmissibleCoefficient l (A n)),
    let F := nativeConstructibleLowerShriek R l D.k
      (exceptionalCurrentFieldCD l D.k (Or.inr inferInstance)) f hR
    let adj := currentExceptionalAdjunction R l D.k (Or.inr inferInstance) f hR
    let ω := (currentExceptionalInverseImage R l D.k (Or.inr inferInstance) f hR).obj
      (IntegralDualizingNative.unit R s)
    let Fn := fun n ↦ rightDerivedLowerShriekOfCompactification (A n) c
    let adjN := fun n ↦ ctfExceptionalAdjunction (A n) l D.k
      (BaseFieldFiniteCD.of_isAlgClosed l D.k) f (hA n)
    let ωn := fun n ↦ (ctfExceptionalInverseImage (A n) l D.k
      (BaseFieldFiniteCD.of_isAlgClosed l D.k) f (hA n)).obj
        (IntegralDualizingNative.finiteUnit (A n) s)
    let red := AdicCompletion.derivedReduction l E X.left
    let a := fun n ↦ (⟨⟨DerivedNakayama.reductionRing l E (n + 1)⟩⟩ :
      (⟨R⟩ : ScalarSixRing.{u}) ⟶ ⟨A n⟩)
    let an := fun n ↦ (⟨⟨AdicCompletion.transitionRing l E n⟩⟩ :
      (⟨A (n + 1)⟩ : ScalarSixRing.{u}) ⟶ ⟨A n⟩)
    letI (n : ℕ) : (AdicCompletion.derivedReduction l E s n).Monoidal :=
      scalarSixChangeMonoidal (a n) s
    letI (n : ℕ) : (AdicCompletion.finiteExtend l E s n).Monoidal :=
      scalarSixChangeMonoidal (an n) s
    let γ := fun n ↦ (scalarCompactSupportMap (a n) c.i c.g).app ω.obj
    let γn := fun n ↦ (scalarCompactSupportMap (an n) c.i c.g).app (ωn (n + 1)).obj
    ∃ e : ∀ n, (red n).obj ω.obj ≅ (ωn n).obj,
         (∀ n, IsIso (γ n) ∧
           γ n ≫ (Fn n).map (e n).hom ≫ ((adjN n).counit.app
             (IntegralDualizingNative.finiteUnit (A n) s)).hom =
           (AdicCompletion.derivedReduction l E s n).map
             (adj.counit.app (IntegralDualizingNative.unit R s)).hom ≫
           (Functor.Monoidal.εIso (AdicCompletion.derivedReduction l E s n)).inv) ∧
         (∀ n, IsIso (γn n) ∧
           γn n ≫ (Fn n).map
             ((AdicCompletion.finiteExtend l E X.left n).map (e (n + 1)).inv ≫
               (AdicCompletion.reductionComp l E X.left n).hom.app ω.obj ≫ (e n).hom) ≫
             ((adjN n).counit.app (IntegralDualizingNative.finiteUnit (A n) s)).hom =
           (AdicCompletion.finiteExtend l E s n).map
             ((adjN (n + 1)).counit.app
               (IntegralDualizingNative.finiteUnit (A (n + 1)) s)).hom ≫
           (Functor.Monoidal.εIso (AdicCompletion.finiteExtend l E s n)).inv) ∧
         (∃ (P : CochainComplex (AdicCompletion.Modules l E X.left) ℤ)
           (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X.left)
             (.up ℤ)).kFlat P) (eP : DerivedCategory.Q.obj P ≅ ω.obj),
           IsIso (AdicCompletion.completionMap l E X.left ω.obj P eP)) ∧
         (letI : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X.left)) :=
            ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete _ I⟩
          let ei := fun n ↦ (AdicCompletion.restrict l E X.left n).mapIso (e n)
          IsDerivedLimit (fun n ↦ (ei (n + 1)).inv ≫
            AdicCompletion.integralStep l E X.left ω.obj n ≫ (ei n).hom) ω.obj) ∧
         IntegralDualizingNative.reductionTorInterval l E X.left
           (-Int.ofNat (2 * d)) 0 ω.obj ∧
         Nonempty (
           (constantModelBoundedConstructible R X.left).ι.op ⋙
             (derivedHom R X.left).flip.obj ω.obj ⋙ CohomologyTransport.Γ R X.left ≅
           F.op ⋙ (constantModelBoundedConstructible R s).ι.op ⋙
             (CohomologyTransport.Γ R s).op ⋙
               coefficientDerivedDual (condensedScalarRing R)) := by
  sorry

end WeilConjectures
