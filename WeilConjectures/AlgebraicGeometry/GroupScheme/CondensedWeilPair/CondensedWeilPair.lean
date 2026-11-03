/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.CondensedVerdierWeilEquivariance
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.ZetaWeil.AdicSmoothDualizing.Condensed.AdicSmoothDualizingComplexes
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilTateFiniteness

/-!
# Condensed Weil pairs

Interface correction of Wei Yang (Zulip #1456, answer to #40, option (a), lead option (ii)):
the Weil complexes of the duality statements are pairs

  `(K, φ : Fr_X^* K ≅ K)`,  `K ∈ D^b_ctf(X_proét, Λ)`,

with Frobenius-compatible morphisms in the underlying derived category, for
`X = X₀ ×_{k₀} k`. The carrier category is the authoritative condensed `D^b_ctf` of the
six operations, `ConstantModelConstructibleFiniteTor Λ X`
(blueprint: det-def-sf-operations, sk-def-sfb-constructible), on which the Brown exceptional
inverse image `ctfExceptionalInverseImage` and its adjunction `ctfExceptionalAdjunction` are
defined (`Sheaf.Paper.CondensedSixOperations`).

* `WeilConjectures.CondensedWeilPair.frobenius`: the exact termwise Frobenius inverse image,
  restricted to `D^b_ctf`;
* `WeilConjectures.CondensedWeilPair.Pair`: the fixed-pair category
  `Endofunctor.IsoAlgebra (frobenius Λ g)`. It carries **no** triangulated or pretriangulated
  instance; arguments with distinguished triangles are made on the underlying condensed derived
  category (`WeilConjectures.CondensedWeilPair.underlying`) with Frobenius-compatible maps;
* `operation`: an operation `L` on `D^b_ctf` with a Frobenius comparison
  `L ⋙ Fr^* ≅ Fr^* ⋙ L` acts on pairs, `(K, φ) ↦ (L K, L(φ) ∘ B_K)`;
* `rightOperation`, `pairAdjunction`: for `L ⊣ R`, the adjoint mate of the inverse comparison
  makes `R` act on pairs, and the geometric adjunction lifts with the same unit and counit;
  its Hom bijection is the bijection of invariant morphisms
  `Hom_Weil(L K, M) ≃ Hom_Weil(K, R M)`;
* `lowerShriek`, `upperShriek`, `lowerShriekUpperShriekAdjunction`: the pair `Rf_!`, the pair
  `Rf^!` (the Brown `Rf^!` with the adjoint-mate Frobenius structure) and the pair adjunction,
  for a morphism `f₀ : X₀ ⟶ Y₀` of separated `k₀`-schemes of finite type.

Source: ~/cc1/bp-follow/wy-1456-answer.txt, steps 1--3; Sun, Ann. Number Theory 6 (2012),
§2.4.2; blueprint: lem-a1-local-boundary-duality, prop-weil-operations,
lem-sf-fixed-pair-adjunction-lift.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.ProEtale.PurityTransport
open CompactSupportComposition
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.CondensedWeilPair

/-! ### The pair category over an automorphism -/

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The Frobenius action `Fr^*` on the condensed `D^b_ctf`: the exact termwise inverse image,
localized, and restricted to the full subcategory (`StrictWeilCondensed.smallAction`).
Source: wy-1456 answer, `Fr_X^* K`; blueprint sk-def-sf-weil-complexes, P_T paragraph. -/
abbrev frobenius {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  StrictWeilCondensed.smallAction Λ g

/-- The Frobenius action on `D^b_ctf` is an autoequivalence.
Source: blueprint sk-def-sf-weil-complexes, inverse clause. -/
theorem frobenius_isEquivalence {T : Scheme.{u}} (g : T ≅ T) :
    (frobenius Λ g).IsEquivalence :=
  StrictWeilCondensed.smallAction_isEquivalence Λ g

/-- The category of condensed Weil pairs `(K, φ : Fr^* K ≅ K)`, `K ∈ D^b_ctf(T, Λ)`, with
Frobenius-compatible morphisms: the fixed-pair category of `frobenius Λ g`
(`StrictWeilCondensed.Complex`). It has no triangulated structure.
Source: wy-1456 answer, the displayed definition of `Weil(X₀, Λ)`; Sun 2012, §2.4.2. -/
abbrev Pair {T : Scheme.{u}} (g : T ≅ T) :=
  Endofunctor.IsoAlgebra (frobenius Λ g)

/-- The underlying `D^b_ctf` object of a pair.
Source: wy-1456 answer, the forgetful functor `(K, φ) ↦ K`. -/
abbrev forget {T : Scheme.{u}} (g : T ≅ T) :
    Pair Λ g ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  Endofunctor.IsoAlgebra.forget (frobenius Λ g)

/-- The underlying object of a pair in the condensed derived category, on which distinguished
triangles of the pair theory are taken.
Source: wy-1456 answer, "arguments involving distinguished triangles should be formulated in the
underlying geometric derived category". -/
def underlying {T : Scheme.{u}} (g : T ≅ T) :
    Pair Λ g ⥤ DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  forget Λ g ⋙ ObjectProperty.ι _

variable {Λ}

/-- A pair from an underlying object and a Frobenius structure.
Source: wy-1456 answer, `(K, φ)`. -/
abbrev mk {T : Scheme.{u}} {g : T ≅ T} (K : ConstantModelConstructibleFiniteTor Λ T)
    (φ : (frobenius Λ g).obj K ≅ K) : Pair Λ g :=
  Endofunctor.IsoAlgebra.mk K φ

/-- An operation on `D^b_ctf` with a Frobenius comparison `B : L ⋙ Fr^* ≅ Fr^* ⋙ L` acts on
pairs by `(K, φ) ↦ (L K, L(φ) ∘ B_K)`, and on morphisms by `L`.
Source: blueprint prop-weil-operations (operation lift); wy-1456 answer, step 2. -/
def operation {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    (L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T')
    (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) : Pair Λ g ⥤ Pair Λ g' :=
  Endofunctor.IsoAlgebra.mapOfNatIso e

/-- The underlying object of `operation L e` is `L` of the underlying object.
Source: definition of the operation lift. -/
def operationForgetIso {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    (L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T')
    (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) :
    operation L e ⋙ forget Λ g' ≅ forget Λ g ⋙ L :=
  Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e

/-- The adjoint mate of the inverse Frobenius comparison of a left adjoint: for `L ⊣ R` and
`B : L ⋙ Fr^* ≅ Fr^* ⋙ L`, the mate `R ⋙ Fr^* ≅ Fr^* ⋙ R` (invertible since both Frobenius
actions are autoequivalences).
Source: wy-1456 answer, step 2 ("`Rf^!` with the corresponding adjoint mate"). -/
def rightComparison {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    {L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T'}
    {R : ConstantModelConstructibleFiniteTor Λ T' ⥤ ConstantModelConstructibleFiniteTor Λ T}
    (adj : L ⊣ R) (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) :
    R ⋙ frobenius Λ g ≅ frobenius Λ g' ⋙ R :=
  haveI := frobenius_isEquivalence Λ g
  haveI := frobenius_isEquivalence Λ g'
  Endofunctor.IsoAlgebra.mateIso adj e

/-- The right adjoint `R` acting on pairs through the adjoint-mate Frobenius structure.
Source: wy-1456 answer, step 2. -/
def rightOperation {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    {L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T'}
    {R : ConstantModelConstructibleFiniteTor Λ T' ⥤ ConstantModelConstructibleFiniteTor Λ T}
    (adj : L ⊣ R) (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) : Pair Λ g' ⥤ Pair Λ g :=
  Endofunctor.IsoAlgebra.mapOfNatIso (rightComparison adj e)

/-- **The pair adjunction.** The geometric adjunction `L ⊣ R` lifts to pairs, with the same
unit and counit; its Hom bijection restricts the geometric one to Frobenius-invariant
morphisms, `Hom_Weil(L K, M) ≃ Hom_Weil(K, R M)`.
Source: wy-1456 answer, step 3; blueprint lem-sf-fixed-pair-adjunction-lift. -/
def pairAdjunction {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    {L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T'}
    {R : ConstantModelConstructibleFiniteTor Λ T' ⥤ ConstantModelConstructibleFiniteTor Λ T}
    (adj : L ⊣ R) (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) :
    operation L e ⊣ rightOperation adj e :=
  haveI := frobenius_isEquivalence Λ g
  haveI := frobenius_isEquivalence Λ g'
  Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction adj e (rightComparison adj e)
    (Endofunctor.IsoAlgebra.mateEquiv_natTrans_eq_mateIso_hom adj e)

/-- The unit of the pair adjunction has the geometric unit as underlying morphism.
Source: wy-1456 answer, step 3, "the unit and counit identities follow from the geometric
adjunction". -/
theorem pairAdjunction_unit_app_hom_f {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    {L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T'}
    {R : ConstantModelConstructibleFiniteTor Λ T' ⥤ ConstantModelConstructibleFiniteTor Λ T}
    (adj : L ⊣ R) (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) (K : Pair Λ g) :
    ((pairAdjunction adj e).unit.app K).hom.f = adj.unit.app K.carrier :=
  rfl

/-- The counit of the pair adjunction has the geometric counit as underlying morphism.
Source: wy-1456 answer, step 3. -/
theorem pairAdjunction_counit_app_hom_f {T T' : Scheme.{u}} {g : T ≅ T} {g' : T' ≅ T'}
    {L : ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T'}
    {R : ConstantModelConstructibleFiniteTor Λ T' ⥤ ConstantModelConstructibleFiniteTor Λ T}
    (adj : L ⊣ R) (e : L ⋙ frobenius Λ g' ≅ frobenius Λ g ⋙ L) (M : Pair Λ g') :
    ((pairAdjunction adj e).counit.app M).hom.f = adj.counit.app M.carrier :=
  rfl

end General

/-! ### Constant pair and internal Hom into a pair -/

section Closed

open MonoidalCategory MonoidalClosed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T : Scheme.{u}} (g : T ≅ T)

/-- The ambient Frobenius action is an autoequivalence.
Source: blueprint sk-def-sf-weil-complexes, inverse clause.
Proof: inverse image along `g` and `g⁻¹` are inverse exact equivalences of module categories
(composition and identity comparisons of inverse image); exact-functor localization descends the
two isomorphisms `g^* (g⁻¹)^* ≅ id`, `(g⁻¹)^* g^* ≅ id` to the derived categories. -/
theorem ambient_isEquivalence :
    (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.IsEquivalence := by
  obtain ⟨⟨e⟩, ⟨e'⟩⟩ := StrictWeilCondensed.action_inverse Λ g
  exact (CategoryTheory.Equivalence.mk (StrictWeilCondensed.action Λ g)
    (StrictWeilCondensed.action Λ g.symm) e.symm e').isEquivalence_functor

/-- The Frobenius structure of an internal Hom into a pair `(W, ψ)`:
`Fr^* RHom(K, W) ≅ RHom(Fr^* K, Fr^* W) ≅ RHom(Fr^* K, W)`, the internal-Hom comparison of the
monoidal autoequivalence `Fr^*` followed by `ψ`.
Source: blueprint sk-def-sf-weil-complexes, contragredient paragraph; wy-1456 answer
(internal Hom on pairs). -/
def homDatum (K W : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (ψ : (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj W ≅ W) :
    (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj ((ihom K).obj W) ≅
      (ihom ((CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj K)).obj W :=
  haveI := ambient_isEquivalence Λ g
  Functor.Monoidal.ihomObjIso (CondensedRing.upperStar Λ g.hom).mapDerivedCategory K W ≪≫
    (ihom ((CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj K)).mapIso ψ

variable {Λ g}

/-- Naturality of the internal-Hom comparison `G [A, B] ⟶ [G A, G B]` of a lax monoidal functor
in the contravariant variable `A`: for `v : A' ⟶ A`,
`G(pre v) ≫ c_{A'} = c_A ≫ pre (G v)`.
Source: `CategoryTheory.Functor.LaxMonoidal.ihomComparison` (mate of the tensorator).
Proof: both sides are maps into `[G A', G B]`; their uncurried forms are computed with
`ihomComparison_ev`, naturality of the tensorator `μ` in both variables and
`id_tensor_pre_app_comp_ev`, and both equal `G v ▷ G [A, B] ≫ μ ≫ G (ev_A)`. -/
theorem ihomComparison_pre {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.LaxMonoidal]
    {A A' : C} (v : A' ⟶ A) (B : C) :
    G.map ((pre v).app B) ≫ (Functor.LaxMonoidal.ihomComparison G A').natTrans.app B =
      (Functor.LaxMonoidal.ihomComparison G A).natTrans.app B ≫
        (pre (G.map v)).app (G.obj B) := by
  apply uncurry_injective
  first
  | (rw [uncurry_pre_app, uncurry_natural_left, uncurry_eq, uncurry_eq,
      Functor.LaxMonoidal.ihomComparison_ev, Functor.LaxMonoidal.ihomComparison_ev,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← G.map_comp, id_tensor_pre_app_comp_ev,
      G.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc]; done)
  | (simp only [uncurry_natural_left, uncurry_pre_app, uncurry_eq, Category.assoc,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whisker_exchange_assoc,
      Functor.LaxMonoidal.ihomComparison_ev, Functor.LaxMonoidal.ihomComparison_ev_assoc,
      Functor.LaxMonoidal.μ_natural_right_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← Functor.map_comp, id_tensor_pre_app_comp_ev, id_tensor_pre_app_comp_ev_assoc]; done)
  | (simp [uncurry_eq, Functor.LaxMonoidal.ihomComparison_ev,
      Functor.LaxMonoidal.ihomComparison_ev_assoc, MonoidalCategory.whisker_exchange_assoc,
      ← Functor.map_comp]; done)

/-- `ihomComparison_pre` followed by post-composition with a map `ψ : G B ⟶ Z`.
Source: as for `ihomComparison_pre`.
Proof: `ihomComparison_pre` and `pre_comm_ihom_map` (`pre` is natural in the target). -/
theorem ihomComparison_pre_comp_map {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D)
    [G.LaxMonoidal] {A A' : C} (v : A' ⟶ A) (B : C) {Z : D} (ψ : G.obj B ⟶ Z) :
    G.map ((pre v).app B) ≫ ((Functor.LaxMonoidal.ihomComparison G A').natTrans.app B ≫
        (ihom (G.obj A')).map ψ) =
      ((Functor.LaxMonoidal.ihomComparison G A).natTrans.app B ≫ (ihom (G.obj A)).map ψ) ≫
        (pre (G.map v)).app Z := by
  first
  | (rw [reassoc_of% (ihomComparison_pre G v B), pre_comm_ihom_map, Category.assoc]; done)
  | (simp only [← Category.assoc, ihomComparison_pre G v B]
     simp only [Category.assoc, pre_comm_ihom_map]; done)

/-- The internal Hom `K ↦ RHom(K, W)` into the underlying object of a pair, as a functor
`(D^b_ctf)ᵒᵖ ⥤ D^b_ctf`, given that it preserves `D^b_ctf` (for `W` the dualizing pair this is
`AlgebraicGeometry.WeilComplex.objectProperty_derivedHom_dualizingComplex_pair`).
Source: blueprint thm-coef-qbar-verdier, `D_X = RHom(-, ω_X)`. -/
def homInto (W : Pair Λ g)
    (hW : ∀ K : ConstantModelConstructibleFiniteTor Λ T,
      (constantModelBoundedConstructible Λ T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((ihom K.obj).obj W.carrier.obj)) :
    (ConstantModelConstructibleFiniteTor Λ T)ᵒᵖ ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ MonoidalClosed.internalHom ⋙
      (CategoryTheory.evaluation _ _).obj W.carrier.obj)
    (fun K ↦ hW K.unop)

/-- The components `Fr^* RHom(K, W) ≅ RHom(Fr^* K, W)` of the Frobenius comparison of
`homInto W`. Source: as for `homDatum`. -/
def homIntoExchangeApp (W : Pair Λ g)
    (hW : ∀ K : ConstantModelConstructibleFiniteTor Λ T,
      (constantModelBoundedConstructible Λ T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((ihom K.obj).obj W.carrier.obj))
    (K : (ConstantModelConstructibleFiniteTor Λ T)ᵒᵖ) :
    (homInto W hW ⋙ frobenius Λ g).obj K ≅ ((frobenius Λ g).op ⋙ homInto W hW).obj K :=
  ObjectProperty.isoMk _
    (homDatum Λ g K.unop.obj W.carrier.obj ((ObjectProperty.ι _).mapIso W.str))

/-- Naturality of `homIntoExchangeApp` in the contravariant variable.
Source: as for `homDatum`.
Proof: `Functor.Monoidal.commIhom` is natural in its target, and the internal-Hom comparison
`LaxMonoidal.ihomComparison` is natural in its source (it is the mate of the tensorator, which is
natural in both variables); the post-composition with `ψ` commutes with pre-composition by any
morphism `K' ⟶ K`, by bifunctoriality of `internalHom`. The inclusion of `D^b_ctf` is fully
faithful, so the equation of ambient morphisms gives the equation in `D^b_ctf`. -/
theorem homIntoExchangeApp_naturality (W : Pair Λ g)
    (hW : ∀ K : ConstantModelConstructibleFiniteTor Λ T,
      (constantModelBoundedConstructible Λ T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((ihom K.obj).obj W.carrier.obj))
    {K K' : (ConstantModelConstructibleFiniteTor Λ T)ᵒᵖ} (v : K ⟶ K') :
    (homInto W hW ⋙ frobenius Λ g).map v ≫ (homIntoExchangeApp W hW K').hom =
      (homIntoExchangeApp W hW K).hom ≫ ((frobenius Λ g).op ⋙ homInto W hW).map v := by
  apply ObjectProperty.hom_ext
  exact ihomComparison_pre_comp_map (CondensedRing.upperStar Λ g.hom).mapDerivedCategory
    v.unop.hom W.carrier.obj W.str.hom.hom

/-- The Frobenius comparison `RHom(-, W) ⋙ Fr^* ≅ Fr^{*,op} ⋙ RHom(-, W)`.
Source: as for `homDatum`. -/
def homIntoExchange (W : Pair Λ g)
    (hW : ∀ K : ConstantModelConstructibleFiniteTor Λ T,
      (constantModelBoundedConstructible Λ T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((ihom K.obj).obj W.carrier.obj)) :
    homInto W hW ⋙ frobenius Λ g ≅ (frobenius Λ g).op ⋙ homInto W hW :=
  NatIso.ofComponents (homIntoExchangeApp W hW) (homIntoExchangeApp_naturality W hW)

/-- **Internal Hom into a pair**: `(K, φ) ↦ (RHom(K, W), RHom(φ⁻¹, ψ) ∘ c)`, contravariant in
`(K, φ)`. With `W` the dualizing pair this is the pair Verdier dual.
Source: wy-1456 answer (internal Hom among the pair operations); blueprint
thm-coef-qbar-verdier. -/
def homPair (W : Pair Λ g)
    (hW : ∀ K : ConstantModelConstructibleFiniteTor Λ T,
      (constantModelBoundedConstructible Λ T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
        ((ihom K.obj).obj W.carrier.obj)) :
    (Pair Λ g)ᵒᵖ ⥤ Pair Λ g :=
  Endofunctor.IsoAlgebra.opFunctor ⋙
    Endofunctor.IsoAlgebra.mapOfNatIso (homIntoExchange W hW)

end Closed

section Constant

open MonoidalCategory

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) {T : Scheme.{u}}
  [CompactSpace T] [QuasiSeparatedSpace T] (g : T ≅ T)

/-- The Frobenius structure of the constant object `Λ_T`: the comparison of `Fr^*` with the
degree-zero functor followed by the inverse unit constraint of the monoidal inverse image.
Source: blueprint sk-def-sf-weil-complexes, `φ_Λ = τ₀`. -/
def constantDatum :
    (CondensedRing.upperStar (c.obj ell) g.hom).mapDerivedCategory.obj (unit ell c T) ≅
      unit ell c T :=
  ((CondensedRing.upperStar (c.obj ell) g.hom).mapDerivedCategorySingleFunctor 0).app
      (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj ell) g.hom)).symm

/-- The constant pair `(Λ_T, φ_Λ)`.
Source: wy-1456 answer, `Λ_s` and the constant object; blueprint sk-def-sf-weil-complexes. -/
def constantPair : Pair (c.obj.{u} ell) g :=
  mk ⟨unit ell c T, AdicSmoothDualizing.Condensed.unit_mem ell c T⟩
    (ObjectProperty.isoMk _ (constantDatum ell c g))

end Constant

/-- The condensed `D^b_ctf` is stable under shifts.
Source: blueprint det-def-sfb-constructible-tor-amplitude (Dctf is a triangulated subcategory).
Proof: boundedness is shift-stable; `H^n(K[m]) ≅ H^{m+n}(K)` and constant-model
constructibility is closed under isomorphism; finite Tor amplitude is a triangulated property
(`constantModelConstructibleFiniteTor_wellDefined`). -/
theorem ctf_shift (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {T : Scheme.{u}}
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (h : (constantModelBoundedConstructible Λ T ⊓
      fun L ↦ DerivedCategory.finiteTorAmplitude _ L) K) (m : ℤ) :
    (constantModelBoundedConstructible Λ T ⊓
      fun L ↦ DerivedCategory.finiteTorAmplitude _ L) (K⟦m⟧) := by
  obtain ⟨⟨hb, hc⟩, ht⟩ := h
  obtain ⟨h1, -, -, -, -, -, -, h8, -⟩ := constantModelConstructibleFiniteTor_wellDefined Λ T
  haveI := h1
  haveI := h8
  refine ⟨⟨DerivedCategory.TStructure.t.bounded.le_shift m K hb, fun n ↦ ?_⟩, ?_⟩
  · exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ T)
      (((DerivedCategory.homologyFunctor _ 0).shiftIso m n (m + n) rfl).app K).symm (hc (m + n))
  · exact (DerivedCategory.finiteTorAmplitude _).le_shift m K ht

section Tate

open MonoidalCategory

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) {T : Scheme.{u}} (g : T ≅ T)
  [∀ x : T, Invertible (ell : T.residueField x)]

/-- The shifted Tate line `Λ_T(d)[2d]` lies in `D^b_ctf`.
Source: blueprint sk-def-sf-weil-complexes (Tate sheaves), cor-pur-adic-and-rational-smooth-
dualizing-complexes (target `Λ(d)[2d]`).
Proof: `StrictWeilCondensed.tate_mem` gives the degree-zero line in `D^b_ctf`; bounded
constant-model constructibility and finite Tor amplitude are stable under shifts (the cohomology
sheaves are reindexed and the Tor interval is translated by `2d`). -/
theorem shiftedTate_mem (d : ℕ) :
    (constantModelBoundedConstructible (c.obj ell) T ⊓
      fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
      ((StrictWeilCondensed.derivedTateLine ell c T d) ⟦2 * (d : ℤ)⟧) :=
  ctf_shift (c.obj ell) _ (StrictWeilCondensed.tate_mem ell c T d) _

/-- The Frobenius structure of `Λ(d)[2d]`: the shift comparison of the exact action followed by
the root-normalized Tate structure `τ_d` shifted by `2d`.
Source: wy-1456 answer, step 4 ("the prescribed `q^{-d}` action on the Tate twist");
blueprint sk-def-sf-weil-complexes, `τ_r`. -/
def shiftedTateDatum (d : ℕ) :
    (StrictWeilCondensed.action (c.obj ell) g).obj
        ((StrictWeilCondensed.derivedTateLine ell c T d) ⟦2 * (d : ℤ)⟧) ≅
      (StrictWeilCondensed.derivedTateLine ell c T d) ⟦2 * (d : ℤ)⟧ :=
  ((StrictWeilCondensed.action (c.obj ell) g).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (StrictWeilCondensed.tateDatum ell c g d)

/-- The pair `(Λ_T(d)[2d], φ_Tate)`.
Source: wy-1456 answer, step 4. -/
def shiftedTatePair (d : ℕ) : Pair (c.obj.{u} ell) g :=
  mk ⟨_, shiftedTate_mem ell c d⟩ (ObjectProperty.isoMk _ (shiftedTateDatum ell c g d))

/-- Tensoring with the Tate line `Λ(m)` in degree zero preserves `D^b_ctf`.
Source: blueprint def-wf-tate-twist (preservation clause), sk-def-sf-weil-complexes.
Proof: the signed Tate line is a locally free module of rank one (trivialized on a primitive-root
cover); derived tensor with its single complex is the exact termwise tensor, which commutes with
cohomology and preserves constructibility locally on the cover
(`nativeLineTensor_finiteness`), hence bounded constant-model constructibility. A Tor-vanishing
interval of `K` against a test module `M` is one of `K ⊗ Λ(m)` against `M ⊗ Λ(-m)`, by
associativity and `Λ(m) ⊗ Λ(-m) ≅ Λ`, so finite Tor amplitude is preserved. This is the first
clause of `StrictWeilCondensed.tate_finiteness` (blueprint: lem-wf-tate-finiteness). -/
theorem tateTwist_mem (m : ℤ) (K : ConstantModelConstructibleFiniteTor (c.obj ell) T) :
    (constantModelBoundedConstructible (c.obj ell) T ⊓
      fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
      (K.obj ⊗ StrictWeilCondensed.derivedTateLine ell c T m) :=
  (StrictWeilCondensed.tate_finiteness ell T).1 c m K.obj K.property

/-- Tensor with the Tate line `Λ(m)` on `D^b_ctf`.
Source: blueprint def-wf-tate-twist, `K(m)`. -/
def ctfTateTwist (m : ℤ) :
    ConstantModelConstructibleFiniteTor (c.obj ell) T ⥤
      ConstantModelConstructibleFiniteTor (c.obj ell) T :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ tensorRight (StrictWeilCondensed.derivedTateLine ell c T m))
    (tateTwist_mem ell c m)

/-- The Frobenius comparison of the Tate twist: the inverse tensorator of the monoidal action
followed by `τ_m` on the Tate factor (as in `WeilTateTwist.ambientTwist`, restricted to
`D^b_ctf`). Source: blueprint def-wf-tate-twist, displayed tensor Weil map. -/
def tateTwistExchange (m : ℤ) :
    ctfTateTwist ell c m ⋙ frobenius (c.obj ell) g ≅
      frobenius (c.obj ell) g ⋙ ctfTateTwist ell c m :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((Functor.Monoidal.commTensorRight (StrictWeilCondensed.action (c.obj ell) g)
          (StrictWeilCondensed.derivedTateLine ell c T m)).symm ≪≫
        Functor.isoWhiskerLeft (StrictWeilCondensed.action (c.obj ell) g)
          ((tensoringRight _).mapIso (StrictWeilCondensed.tateDatum ell c g m))))

/-- **The Tate twist of condensed Weil pairs** `(K, φ) ↦ (K ⊗ Λ(m), (φ ⊗ τ_m) ∘ μ⁻¹)`.
Source: blueprint def-wf-tate-twist; wy-1456 answer (pair operations). -/
def tateTwist (m : ℤ) : Pair (c.obj.{u} ell) g ⥤ Pair (c.obj ell) g :=
  operation (ctfTateTwist ell c m) (tateTwistExchange ell c g m)

end Tate

section SheafEmbedding

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {T : Scheme.{u}} (g : T ≅ T)

/-- Weil modules `(M, θ : g^* M ≅ M)` whose degree-zero complex lies in `D^b_ctf` (constructible
Weil sheaves with flat, e.g. lisse, carrier; any constructible Weil sheaf at field
coefficients). Source: blueprint def-weil-weil-sheaf-complex, degree-zero clause. -/
abbrev SheafProperty : ObjectProperty (WeilConjectures.condensedWeilModules Λ g.hom) :=
  fun M ↦ (constantModelBoundedConstructible Λ T ⊓
    fun L ↦ DerivedCategory.finiteTorAmplitude _ L)
    ((DerivedCategory.singleFunctor _ 0).obj M.carrier)

/-- The Frobenius structure of a Weil sheaf placed in degree zero: the comparison of the derived
Frobenius with the degree-zero functor, followed by `θ`.
Source: blueprint def-weil-weil-sheaf-complex, degree-zero clause. -/
def sheafDatum (M : WeilConjectures.condensedWeilModules Λ g.hom) :
    (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ≅
      (DerivedCategory.singleFunctor _ 0).obj M.carrier :=
  ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app M.carrier ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso M.str

/-- Morphisms of Weil modules give Frobenius-compatible maps of the degree-zero complexes.
Proof: naturality of the degree-zero comparison `mapDerivedCategorySingleFunctor 0` turns
`D(g^*)(u[0]) ≫ comparison_N` into `comparison_M ≫ (g^* u)[0]`; then `g^* u ≫ θ_N = θ_M ≫ u`
(the morphism condition of `u`) and functoriality of the degree-zero functor give the
equation. -/
theorem sheafDatum_comm {M N : WeilConjectures.condensedWeilModules Λ g.hom} (u : M ⟶ N) :
    (CondensedRing.upperStar Λ g.hom).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor _ 0).map u.hom.f) ≫ (sheafDatum Λ g N).hom =
      (sheafDatum Λ g M).hom ≫ (DerivedCategory.singleFunctor _ 0).map u.hom.f := by
  have h1 := ((CondensedRing.upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).hom.naturality
    u.hom.f
  have h2 : (CondensedRing.upperStar Λ g.hom).map u.hom.f ≫ N.str.hom = M.str.hom ≫ u.hom.f :=
    u.hom.h
  simp only [Functor.comp_map] at h1
  simp only [sheafDatum, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [reassoc_of% h1, Category.assoc, ← Functor.map_comp, h2, Functor.map_comp]

/-- **The embedding of Weil sheaves as condensed Weil pairs in degree zero**
`(M, θ) ↦ (M[0], θ[0])`.
Source: wy-1456 answer (lisse/constructible Weil-sheaf embedding among the pair operations);
blueprint def-weil-weil-sheaf-complex. -/
def sheafToPair : (SheafProperty Λ g).FullSubcategory ⥤ Pair Λ g where
  obj M := mk ⟨_, M.property⟩ (ObjectProperty.isoMk _ (sheafDatum Λ g M.obj))
  map {M N} u := ObjectProperty.homMk
    { f := ObjectProperty.homMk ((DerivedCategory.singleFunctor _ 0).map u.hom.hom.f)
      h := ObjectProperty.hom_ext _ (sheafDatum_comm Λ g u.hom) }
  map_id M := by
    refine ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ObjectProperty.hom_ext _ ?_))
    first
    | exact (DerivedCategory.singleFunctor
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) 0).map_id
          M.obj.carrier
    | (dsimp only; exact Functor.map_id _ _)
    | simp
  map_comp u v := by
    refine ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ObjectProperty.hom_ext _ ?_))
    first
    | exact (DerivedCategory.singleFunctor
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) 0).map_comp
          u.hom.hom.f v.hom.hom.f
    | (dsimp only; exact Functor.map_comp _ _ _)
    | simp

end SheafEmbedding

/-- A morphism of separated schemes over `S` is separated.
Proof: `f.left ≫ Y.hom = X.hom` is separated, and separatedness cancels on the right
(`IsSeparated.of_comp`). -/
instance overHomLeft_isSeparated {S : Scheme.{u}} {X Y : Over S} [IsSeparated X.hom]
    (f : X ⟶ Y) : IsSeparated f.left := by
  have : IsSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact IsSeparated.of_comp f.left Y.hom

/-- A morphism between schemes locally of finite type over `S` is locally of finite type.
Proof: right cancellation `locallyOfFiniteType_of_comp` for `f.left ≫ Y.hom = X.hom`. -/
instance overHomLeft_locallyOfFiniteType {S : Scheme.{u}} {X Y : Over S}
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) : LocallyOfFiniteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact locallyOfFiniteType_of_comp f.left Y.hom

/-- A morphism from a quasi-compact to a quasi-separated scheme over `S` is quasi-compact.
Proof: right cancellation `QuasiCompact.of_comp` for `f.left ≫ Y.hom = X.hom`, `Y.hom`
separated hence quasi-separated. -/
instance overHomLeft_quasiCompact {S : Scheme.{u}} {X Y : Over S} [QuasiCompact X.hom]
    [IsSeparated Y.hom] (f : X ⟶ Y) : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  exact QuasiCompact.of_comp f.left Y.hom

/-! ### Condensed Weil pairs on `X₀ ×_{k₀} k` -/

section Geometric

variable (D : FiniteFieldDatum.{u})

/-- The geometric Frobenius `Fr_X = id_{X₀} × σ⁻¹` of `X = X₀ ×_{k₀} k`, as an automorphism;
its morphism is `D.purityGaloisMap X₀`.
Source: blueprint def-pur-scheme-geometric-frobenius; Deligne, Weil II (1.1.7). -/
abbrev geometricFrobenius (X₀ : Over (Spec (.of D.k₀))) :
    (D.purityFrobeniusFiber X₀).left ≅ (D.purityFrobeniusFiber X₀).left :=
  StrictWeilCondensed.modelFrobenius D X₀

/-- The finite base `Spec k₀` as a model over itself.
Source: `ω_X = Ra_X^! Λ_s` (blueprint: thm-coef-qbar-verdier). -/
abbrev point : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

instance pointFiniteType : LocallyOfFiniteType (point D).hom := by
  change LocallyOfFiniteType (𝟙 (Spec (.of D.k₀)))
  infer_instance

instance pointQuasiCompact : QuasiCompact (point D).hom := by
  change QuasiCompact (𝟙 (Spec (.of D.k₀)))
  infer_instance

instance pointSeparated : IsSeparated (point D).hom := by
  change IsSeparated (𝟙 (Spec (.of D.k₀)))
  infer_instance

instance pointCompactSpace : CompactSpace (D.purityFrobeniusFiber (point D)).left :=
  QuasiCompact.compactSpace_of_compactSpace (D.purityFrobeniusFiber (point D)).hom

instance pointNoetherian : IsNoetherian (D.purityFrobeniusFiber (point D)).left :=
  isNoetherian_of_locallyOfFiniteType (D.purityFrobeniusFiber (point D)).hom

/-- The structure morphism `a₀ : X₀ ⟶ Spec k₀` as a morphism of models.
Source: `ω_X = Ra_X^! Λ_s`. -/
abbrev structureArrow (X₀ : Over (Spec (.of D.k₀))) : X₀ ⟶ point D := Over.homMk X₀.hom

variable (ell : ℕ) [Fact ell.Prime]

/-- The category `Weil(X₀, Λ)` of condensed Weil pairs on `X = X₀ ×_{k₀} k` with coefficients
`Λ = c.obj ell` (integral, rational, or `ℚ̄_ℓ` condensed coefficients).
Source: wy-1456 answer, displayed definition; blueprint sk-def-sf-weil-complexes. -/
abbrev WeilPair (c : Coefficient ell) (X₀ : Over (Spec (.of D.k₀))) :=
  Pair (c.obj.{u} ell) (geometricFrobenius D X₀)

variable (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
  (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
  (hΛ : IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell))
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)

/-- The geometric morphism `f = f₀ ×_{k₀} k`, a morphism of separated `k`-schemes of finite
type.
Source: blueprint def-pur-scheme-geometric-frobenius, the base-change squares. -/
abbrev geometricMap :
    D.purityFrobeniusFiber X₀ ⟶ D.purityFrobeniusFiber Y₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀

include hEll hΛ in
end Geometric

/-! ### Compact support and exceptional inverse image on condensed Weil pairs

At field coefficients (`E` or `ℚ̄_ℓ`, hypothesis `hField`) the Frobenius comparison of `Rf_!` is
the canonical proper/open exchange `canonicalSupportExchange` of
`cor-coef-verdier-weil-equivariance`, the one with which `verdier_weil_equivariance` is stated. -/

section Shriek

open StrictWeilCondensed

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)]
  (c : Coefficient ell) (hΛ : IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell))
  (hField : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk (c.bundled.{u} ell).X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
    Nonempty (Mon.mk (c.bundled.{u} ell).X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)

end Shriek

end WeilConjectures.CondensedWeilPair
