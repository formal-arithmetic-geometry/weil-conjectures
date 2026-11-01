/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.CategoryTheory.SixFunctors.EvaluationShiftTransport
import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleDevissageSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleHomSingle
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Topology.NoetherianSpace
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.CategoryTheory.RingedHomUniverses.RHomContinuityTriangleClosure
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Order.CompletePartialOrder
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteStrictPerfectHom
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.SixFunctors.InternalHomLocalizationComparison
import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralDerivedUnit
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralComplexTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.PrincipalReductionDerivedNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
import WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import WeilConjectures.ProEtaleCoefficients.SfbHomFilteredColimit.StrictHomNumeratorTranspose
import WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.CategoryTheory.ScalarHomDerivedCoherence.ScalarHomDerivedSquareCoherence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.InternalSectionScalarHomTransportData
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.Ring.RingObjectSheaf
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Constructible internal Hom and coefficient comparison

Source: Bhatt--Scholze, Lemmas 6.7.13, 6.8.13, Proposition 6.8.14(2),
Remark 6.8.15; Hemo--Richarz--Scholbach, Theorem 7.7, Lemma 7.9, Remark 7.10.
The closure has the finite-subextension-valued condensed structure.
(blueprint: lem-per-constructible-coefficient-hom-comparison)
-/

public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

variable (X : Scheme.{u})
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- The ordinary ambient derived category over the pulled-back coefficient ring.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev D (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj R X))

/-- The recorded finite-constant-local-model bounded constructibility predicate.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev bc (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] := constantModelBoundedConstructible R X

/-- Ordinary derived internal Hom, with no completion or restriction to chosen models.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev hom (K L : D X R) : D X R :=
  ((CondensedRing.derivedHom R X).obj (op K)).obj L

/-- The counit of the recorded ordinary derived tensor--Hom adjunction.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def evaluation (K L : D X R) : K ⊗ hom X K L ⟶ L :=
  (CondensedRing.derivedTensorHomAdjunction R K).counit.app L

/-- Derived scalar extension along the actual pulled-back ring map.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev scalar (a : R ⟶ S) [IsMonHom a] : D X R ⥤ D X S :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor

/-- The canonical strong monoidal structure obtained by deriving balanced scalar tensor.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose, instance_reducible]
def scalarMonoidal (a : R ⟶ S) [IsMonHom a] : (scalar X a).Monoidal :=
  letI := CondensedRing.internalScalarMonoidal a X
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorMonoidal

/-- The balanced tensorator; it is defined also for nonflat finite quotient maps.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def tensorator (a : R ⟶ S) [IsMonHom a] (K L : D X R) :
    (scalar X a).obj K ⊗ (scalar X a).obj L ⟶ (scalar X a).obj (K ⊗ L) :=
  letI := scalarMonoidal X a
  Functor.LaxMonoidal.μ (scalar X a) K L

/-- The actual scalar--Hom map: transpose of tensorator followed by scalar evaluation.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def comparison (a : R ⟶ S) [IsMonHom a] (K L : D X R) :
    (scalar X a).obj (hom X K L) ⟶
      hom X ((scalar X a).obj K) ((scalar X a).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction S ((scalar X a).obj K)).homEquiv _ _
    (tensorator X a K (hom X K L) ≫ (scalar X a).map (evaluation X K L))

/-- The actual relative bidual arrow, transposing evaluation after the Koszul symmetry.
This definition makes no assertion of invertibility.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def bidual (K W : D X R) : K ⟶ hom X (hom X K W) W :=
  MonoidalClosed.curry ((β_ (hom X K W) K).hom ≫ evaluation X K W)

/-- Composition of internal morphisms, transposed from the two evaluation maps.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def composition (K L M : D X R) :
    hom X K L ⊗ hom X L M ⟶ hom X K M :=
  MonoidalClosed.curry
    ((α_ K (hom X K L) (hom X L M)).inv ≫
      (evaluation X K L ⊗ₘ 𝟙 (hom X L M)) ≫ evaluation X L M)

/-- Tensoring internal morphisms. Its middle interchange is the native Koszul braiding.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def tensorHom (K L P Q : D X R) :
    hom X K L ⊗ hom X P Q ⟶ hom X (K ⊗ P) (L ⊗ Q) :=
  MonoidalClosed.curry
    (tensorμ K P (hom X K L) (hom X P Q) ≫
      (evaluation X K L ⊗ₘ evaluation X P Q))

/-- The integral coefficient ring in the spectral presentation used by derived completion.
The universe lift changes only its presentation, not the embedded coefficient field.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev integral (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedNakayama.integerRing.{u} ℓ (ULift.{u} E.val)

/-- The canonical continuous integer-ring isomorphism, induced by the lifted inclusion.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
def integralIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Profinite.padicIntegersRingObj.{u} ℓ E.val ≅ integral.{u} ℓ E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (AlgebraicGeometry.ProEtale.integerRingSheafIso ℓ E)

/-- The actual inclusion of integral coefficients into the embedded finite field,
transported along the canonical spectral/embedded integer isomorphism.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev integralToField (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    integral.{u} ℓ E ⟶ Profinite.continuousMapRingObj.{u} E.val :=
  (integralIso ℓ E).inv ≫ padicIntegersRingObjToContinuousMapRingObj ℓ E

/-- The quotient at exponent n+1; hence index zero means the first positive reduction.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev finite (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  DerivedNakayama.quotientRing.{u} ℓ (ULift.{u} E.val) (n + 1)

/-- The actual uniformizer-power quotient map, with no arbitrary choice of scalar map.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev reductionMap (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :=
  DerivedNakayama.reductionRing.{u} ℓ (ULift.{u} E.val) (n + 1)

/-- The signed Tate line in the native module encoding, placed in degree zero.
This uses the recorded signed-power construction and its section-module equivalence.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def signedLine (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (n : ℤ) : D X R :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj R X)).inverse.obj
        (spSignedTwist X _ L n))

/-- The actual integral Tate line, transported to the completion coefficient presentation.
Source: the coefficient paragraphs of blueprint `thm-a1-curve-perverse-heart`, Step 3;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def integralLine (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (Mod.comap (coefficientMap (integralIso.{u} ℓ E).inv X)).obj (spIntegralTwist X ℓ E)

/-- Closure under ordinary internal Hom in the full bounded constructible category.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def HomClosed (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ K L : D X R, bc X R K → bc X R L → bc X R (hom X K L)

/-- Bounded constructible finite-Tor origin on the actual small étale site.
The encoding is constrained by its constant-section normalization, not arbitrary.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def FiniteEtaleOrigin (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (K : D X (finite.{u} ℓ E n)) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI := AdicCompletion.finiteTopology ℓ (ULift.{u} E.val) (n + 1)
  ∃ enc : FiniteDiscreteOrdinary.Encoding
      (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1)) X,
    ∃ J : DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1))))),
      DerivedCategory.TStructure.t.bounded J ∧
      (∀ i : ℤ, Scheme.IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ i).obj J)) ∧
      DerivedCategory.finiteTorAmplitude _ J ∧
      Nonempty ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) (n + 1)))) X).mapDerivedCategory.obj
            J ≅
            enc.fixedDerived.functor.obj K)

/-- Integral completeness means the recorded canonical completion map is invertible.
Every positive finite reduction has the exact constructibility, Tor and origin clauses.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def IntegralAssertions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Prop :=
  ∀ K : D X (integral.{u} ℓ E), bc X (integral ℓ E) K →
    IsDerivedComplete ℓ (ULift.{u} E.val) X K ∧
    ∀ n : ℕ,
      bc X (finite ℓ E n) ((scalar X (reductionMap ℓ E n)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((scalar X (reductionMap ℓ E n)).obj K) ∧
      FiniteEtaleOrigin X ℓ E n ((scalar X (reductionMap ℓ E n)).obj K)

/-- Evaluation, Koszul symmetry, composition and the actual arbitrary-target bidual
commute with the specified scalar comparison. There is no bidual invertibility clause.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def EvaluationCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ K L : D X R,
    tensorator X a K (hom X K L) ≫ (scalar X a).map (evaluation X K L) =
      (𝟙 ((scalar X a).obj K) ⊗ₘ comparison X a K L) ≫
        evaluation X ((scalar X a).obj K) ((scalar X a).obj L)) ∧
  (∀ K L : D X R,
    tensorator X a K L ≫ (scalar X a).map (β_ K L).hom =
      (β_ ((scalar X a).obj K) ((scalar X a).obj L)).hom ≫ tensorator X a L K) ∧
  (∀ K L M : D X R,
    tensorator X a (hom X K L) (hom X L M) ≫
        (scalar X a).map (composition X K L M) ≫ comparison X a K M =
      (comparison X a K L ⊗ₘ comparison X a L M) ≫
        composition X ((scalar X a).obj K) ((scalar X a).obj L) ((scalar X a).obj M)) ∧
  (∀ K W : D X R, bc X R K → bc X R W →
    (scalar X a).map (bidual X K W) ≫ comparison X a (hom X K W) W =
      bidual X ((scalar X a).obj K) ((scalar X a).obj W) ≫
        ((CondensedRing.derivedHom S X).map (comparison X a K W).op).app
          ((scalar X a).obj W))

/-- The target-Hom shift is the right-adjoint mate of the native derived tensor shift.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def targetShift (K L : D X R) (n : ℤ) :
    hom X K (L⟦n⟧) ≅ (hom X K L)⟦n⟧ :=
  letI := (ihom.adjunction K).rightAdjointCommShift ℤ
  ((ihom K).commShiftIso n).app L

/-- Compatibility with both integer shifts, including the signed opposite exact
source shift. The same Koszul shift conventions are used on both sides.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def ShiftCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ (K L : D X R) (n : ℤ),
    (scalar X a).map (targetShift X K L n).hom ≫
        ((scalar X a).commShiftIso n).hom.app (hom X K L) ≫
          (shiftFunctor (D X S) n).map (comparison X a K L) =
      comparison X a K (L⟦n⟧) ≫
        (ihom ((scalar X a).obj K)).map (((scalar X a).commShiftIso n).hom.app L) ≫
          (targetShift X ((scalar X a).obj K) ((scalar X a).obj L) n).hom) ∧
  (∀ (K L : D X R) (n : ℤ),
    (scalar X a).map (siteHomSignedSourceComponent L n (op K)) ≫
        ((scalar X a).commShiftIso n).hom.app (hom X K L) ≫
          (shiftFunctor (D X S) n).map (comparison X a K L) =
      comparison X a (K⟦-n⟧) L ≫
        ((CondensedRing.derivedHom S X).map
          (((scalar X a).commShiftIso (-n)).inv.app K).op).app ((scalar X a).obj L) ≫
          siteHomSignedSourceComponent ((scalar X a).obj L) n (op ((scalar X a).obj K)))

/-- Naturality in both inputs, as an equality of actual internal-sheaf morphisms.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def NaturalComparison (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ (K K' L L' : D X R) (f : K' ⟶ K) (g : L ⟶ L'),
    (scalar X a).map (((CondensedRing.derivedHom R X).map f.op).app L ≫
      ((CondensedRing.derivedHom R X).obj (op K')).map g) ≫ comparison X a K' L' =
    comparison X a K L ≫
      ((CondensedRing.derivedHom S X).map ((scalar X a).map f).op).app
        ((scalar X a).obj L) ≫
      ((CondensedRing.derivedHom S X).obj (op ((scalar X a).obj K'))).map
        ((scalar X a).map g)

/-- Full-category preservation, invertibility and coherence of scalar--Hom comparison.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def ScalarAssertions (a : R ⟶ S) [IsMonHom a] : Prop :=
  (∀ K : D X R, bc X R K → bc X S ((scalar X a).obj K)) ∧
  (∀ K L : D X R, bc X R K → bc X R L → IsIso (comparison X a K L)) ∧
  EvaluationCoherence X a ∧ ShiftCoherence X a ∧ NaturalComparison X a

/-- The canonical successive-scalar identification, defined by the existing derived
change-of-rings adjunction and its normalized restriction composition.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def scalarTower
    {T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj T] [IsCommMonObj T]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b] :
    scalar X (a ≫ b) ≅ scalar X a ⋙ scalar X b :=
  Mod.derivedExtendScalarsCompIso (coefficientMap a X) (coefficientMap b X)
    (coefficientMap (a ≫ b) X) (coefficientMap_comp a b X).symm

/-- Direct-versus-successive scalar comparison, including the actual canonical
composition transport, rather than existence of some identifying isomorphism.
Source: Bhatt--Scholze 6.7.13, 6.8.13--15; blueprint Step 3 of
`thm-a1-curve-perverse-heart` and `det-pd-biduality-coefficients` (ii)--(iv)
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TowerCoherence
    {T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj T] [IsCommMonObj T]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b] : Prop :=
  ∀ K L : D X R,
    (scalarTower X a b).hom.app (hom X K L) ≫
        (scalar X b).map (comparison X a K L) ≫
        comparison X b ((scalar X a).obj K) ((scalar X a).obj L) =
      comparison X (a ≫ b) K L ≫
        ((CondensedRing.derivedHom T X).map ((scalarTower X a b).inv.app K).op).app
          ((scalar X (a ≫ b)).obj L) ≫
        ((CondensedRing.derivedHom T X).obj
          (op ((scalar X b).obj ((scalar X a).obj K)))).map
            ((scalarTower X a b).hom.app L)

/-- The identity-coefficient identification induced by the scalar-unit adjunction.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def scalarIdentity
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : scalar X (𝟙 R) ≅ 𝟭 (D X R) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (𝟙 R) X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_id X) ≪≫ Mod.comapId (condensedRingObj R X)) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm)

/-- The exact identity normalization of the evaluation-transpose comparison.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def IdentityCoherence
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] : Prop :=
  ∀ K L : D X R,
    comparison X (𝟙 R) K L ≫
        ((CondensedRing.derivedHom R X).map ((scalarIdentity X R).inv.app K).op).app
          ((scalar X (𝟙 R)).obj L) ≫
        ((CondensedRing.derivedHom R X).obj (op K)).map ((scalarIdentity X R).hom.app L) =
      (scalarIdentity X R).hom.app (hom X K L)

/-- The native derived pullback along a scheme isomorphism, with its canonical monoidal
structure. The definition uses the actual inverse-image functor, not an abstract equivalence.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev pull {Y : Scheme.{u}}
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : X ≅ Y) : D Y R ⥤ D X R :=
  (CondensedRing.upperStar R e.hom).leftDerivedFunctor

/-- The evaluation-transpose internal-Hom comparison for the actual scheme pullback.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def pullComparison {Y : Scheme.{u}}
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : X ≅ Y) (K L : D Y R) :
    (pull X R e).obj (hom Y K L) ⟶ hom X ((pull X R e).obj K) ((pull X R e).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction R ((pull X R e).obj K)).homEquiv _ _
    (Functor.LaxMonoidal.μ (pull X R e) K (hom Y K L) ≫
      (pull X R e).map (evaluation Y K L))

/-- The normalized scalar/pullback interchange, valid even for nonflat quotients.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
abbrev pullScalar {Y : Scheme.{u}} (a : R ⟶ S) [IsMonHom a] (e : X ≅ Y) :
    pull X R e ⋙ scalar X a ≅ scalar Y a ⋙ pull X S e :=
  CondensedRing.derivedUpperStarExtendScalarsIso a e.hom

/-- Commutation with scheme isomorphisms as the actual square on internal Hom.
It retains both first-input contravariance and the specified scalar/pullback interchange.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def SchemeCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ (Y : Scheme.{u}) (e : X ≅ Y) (K L : D Y R),
    (pullScalar X a e).hom.app (hom Y K L) ≫
        (pull X S e).map (comparison Y a K L) ≫
        pullComparison X S e ((scalar Y a).obj K) ((scalar Y a).obj L) =
      (scalar X a).map (pullComparison X R e K L) ≫
        comparison X a ((pull X R e).obj K) ((pull X R e).obj L) ≫
        ((CondensedRing.derivedHom S X).map ((pullScalar X a e).inv.app K).op).app
          ((scalar X a).obj ((pull X R e).obj L)) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((pull X S e).obj ((scalar Y a).obj K)))).map
            ((pullScalar X a e).hom.app L)

/-- Tensor-Hom compatibility. Specializing P and Q to the constructed signed Tate
lines gives the Tate-twist square, with exactly the balanced evaluations and Koszul signs.
It also applies to their finite quotient reductions.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TensorCoherence (a : R ⟶ S) [IsMonHom a] : Prop :=
  ∀ K L P Q : D X R,
    tensorator X a (hom X K L) (hom X P Q) ≫
        (scalar X a).map (tensorHom X K L P Q) ≫ comparison X a (K ⊗ P) (L ⊗ Q) ≫
        ((CondensedRing.derivedHom S X).map (tensorator X a K P).op).app
          ((scalar X a).obj (L ⊗ Q)) =
      (comparison X a K L ⊗ₘ comparison X a P Q) ≫
        tensorHom X ((scalar X a).obj K) ((scalar X a).obj L)
          ((scalar X a).obj P) ((scalar X a).obj Q) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((scalar X a).obj K ⊗ (scalar X a).obj P))).map (tensorator X a L Q)

/-- All coherence clauses for a specified actual coefficient map. Tower coherence
is formal even if the second comparison is not invertible; the displayed field and quotient
maps themselves are required to be invertible on the full constructible categories.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def CoherentScalarAssertions (a : R ⟶ S) [IsMonHom a] : Prop :=
  ScalarAssertions X a ∧ TensorCoherence X a ∧ SchemeCoherence X a ∧
  IdentityCoherence X R ∧ IdentityCoherence X S ∧
  ∀ (T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj T] [IsCommMonObj T] (b : S ⟶ T) [IsMonHom b], TowerCoherence X a b

/-- For the actual Tate lines the tensor-Hom comparison is invertible. Thus the
preceding tensor square is the signed Tate compatibility, rather than just an equation
after forgetting the line. Both positive and negative powers and degree zero are included.
Source: blueprint Step 3 of `thm-a1-curve-perverse-heart`, coefficient paragraphs;
Stacks Tags 08J9, 07A4 and 0FPT
(blueprint: lem-per-constructible-coefficient-hom-comparison).
-/
@[expose]
def TateAssertions
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (line : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) : Prop :=
  (∀ n : ℤ, bc X R (signedLine X R line n)) ∧
  ∀ (K L : D X R), bc X R K → bc X R L → ∀ m n : ℤ,
    IsIso (tensorHom X K L (signedLine X R line m) (signedLine X R line n))

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
