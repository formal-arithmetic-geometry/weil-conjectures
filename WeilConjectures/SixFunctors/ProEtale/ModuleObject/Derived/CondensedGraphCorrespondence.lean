/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.TraceOperations.GeometricOperationPackage
public import WeilConjectures.DeligneLaumon.FiniteTraceGraphCorrespondence

/-!
# The condensed graph correspondence and its scalar functoriality

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-thm-tf-uniform-formula/sk-thm-tf-uniform-formula.proof.md,
operator-identification sentence: extension of the graph correspondence construction to
condensed coefficients (blueprint: lem-trf-condensed-graph-correspondence-base-change).

Over a finite or algebraically closed field `k` of characteristic `p ≠ ℓ`, for a separated
finite-type `k`-scheme `X`, a proper `k`-endomorphism `h` and `K` in the bounded constructible
finite-Tor category, a map `v : Lh^* K → K` gives the graph endocorrespondence
`C = X`, `c₁ = id_X`, `c₂ = h`, `u = ι_{X,K} ∘ v` of the graph-operator construction of
`sk-d-operator`, now read with the ordinary condensed six operations. Here `ι_{X,K}` is the
unit of `R(id_X)_! ⊣ R(id_X)^!` transported across `R(id_X)_! ≃ id`. The maps of the graph
operator composite are the pullback unit, the proper comparison `P₂`, the compact-support
composition comparisons `μ₁, μ₂`, the coefficient map and the exceptional counit; under a listed
scalar extension each of them, and `ι` and `u`, are carried to the corresponding map after
extension. Nothing here asserts an equality of graph operators or a stalk formula.

All operations are the existing ones: `ctfLowerShriek` / `ctfExceptionalInverseImage` /
`ctfExceptionalAdjunction` (the restricted adjunction of `sk-thm-existence`),
`RootCoordinateFace.adjunction` (`f^* ⊣ Rf_*`), `moduleObjectDerivedPullback` (`Lf^*`), and the
compactification comparison and composition isomorphisms of the chosen witness package
`compCompositionWitnesses` of `sk-thm-sf-comp-composition`. The base `s = Spec k` and the
structure maps are the `sk-d-six` conventions `TraceOperations.base` and
`TraceOperations.structureMap`.
The construction is uniform in the admissible coefficient; at a finite discrete coefficient it has
the data of the finite graph correspondence `WeilConjectures.finiteTrfGraphCorrespondence`.

## Main definitions

- `condensedGraphIdentityUnit`: the identity exceptional unit `ι_{X,K} : K → R(id_X)^! K`.
- `condensedGraphCoefficient`: the graph coefficient map `u = ι_{X,K} ∘ v`.
- `condensedGraphProperComparison`: the proper comparison `P₂ : Rh_! ≃ Rh_*`.
- `condensedGraphCompositionComparison`: the composition comparisons `μ₁` (`f = id`) and
  `μ₂` (`f = h`).

## Main statements

- `condensedGraphCorrespondence_scalarExtension`: scalar functoriality of all these maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The base `s = Spec k`, i.e. the `sk-d-six` base object `TraceOperations.base`, as an object
of the standing separated finite-type setting.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; `RΓ_c = Ra_{X!}` over
`s = Spec k` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphBase (k : Type u) [Field k] : SepFinType k :=
  ⟨TraceOperations.base (Spec (.of k)),
    ⟨inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k)))),
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k)))),
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))⟩⟩

/-- The structure map `a_X : X → Spec k`, i.e. `TraceOperations.structureMap X`, as a morphism
of the standing separated finite-type setting.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; the structure map
`a_X` of `sk-d-operator` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphStructureMap {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    SepFinType.mk X ⟶ condensedGraphBase k :=
  ObjectProperty.homMk (TraceOperations.structureMap X)

/-- The base structure morphism `Spec k → Spec k` (the identity) is quasi-compact, stated at
the base object `condensedGraphBase k` so that instance search sees through `Over.mk`.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; the base
`s = Spec k` of `sk-d-six` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
instance condensedGraphBase_quasiCompact (k : Type u) [Field k] :
    QuasiCompact (condensedGraphBase k).obj.hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

/-- The base structure morphism is separated (see `condensedGraphBase_quasiCompact`).
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence
(blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
instance condensedGraphBase_isSeparated (k : Type u) [Field k] :
    IsSeparated (condensedGraphBase k).obj.hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The identity of a separated finite-type `k`-scheme, as a morphism of `SepFinType k`, has a
quasi-compact underlying scheme map.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; the leg
`c₁ = id_X` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
instance condensedGraphIdentity_quasiCompact {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    QuasiCompact (SepFinType.homMk (𝟙 X)).hom.left :=
  inferInstanceAs (QuasiCompact (𝟙 X.left))

/-- The chosen compactification of `a_X`, the one defining `Ra_{X!} = RΓ_c(X, -)`.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; chosen
compactification of `sk-thm-existence`
(blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphStructureCompactification {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    Compactification (condensedGraphStructureMap X).hom.left := by
  letI : QuasiCompact (condensedGraphBase k).obj.hom :=
    (condensedGraphBase k).property.2.1
  exact compactificationOverField (condensedGraphStructureMap X).hom

/-- The chosen compactification of `a_X` read as a compactification of `a_X ∘ f`, for a
`k`-endomorphism `f` (so `a_X f = a_X`): the target `R(a_X f)_! = Ra_{X!}` of `μ`.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; `a_X c_i = a_C`
in `sk-d-operator` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphCompositeCompactification {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] (f : X ⟶ X) :
    Compactification ((SepFinType.homMk f).hom.left ≫ (condensedGraphStructureMap X).hom.left) :=
  (condensedGraphStructureCompactification X).copy (Over.w f)

/-- A bounded constructible finite-Tor object as an object of its localizing closure, by the
defining universal property of the closure (the domain of the comparison isomorphisms).
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; `D_ctf` inside the
domain of `sk-thm-sf-comp-composition`
(blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphLocalizing (Λ : ScalarSixRing.{u}) {Y : Scheme.{u}}
    (L : ConstantModelConstructibleFiniteTor Λ.X Y) :
    (localizingClosureProEtale Λ.X Y).FullSubcategory :=
  ⟨L.obj, fun _ _ hS ↦ hS _ L.property⟩

section Construction

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] (hk : Finite k ∨ IsAlgClosed k)
  (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The identity exceptional unit `ι_{X,K} : K → R(id_X)^! K`: the unit of
`R(id_X)_! ⊣ R(id_X)^!` at `K` transported across `R(id_X)_! ≃ id`. The latter is the
compactification comparison from the chosen compactification of `id_X` to the trivial one
`(id_X, id_X)`, followed by the canonical identity comparison of the trivial compactification.
Concretely it is the adjunction transpose of that composite.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; the identity
exceptional unit (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
def condensedGraphIdentityUnit (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    K ⟶ (ctfExceptionalInverseImage Λ.X ell k (WeilConjectures.exceptionalCurrentFieldCD ell k hk)
      (𝟙 X) hΛ).obj K :=
  ((ctfExceptionalAdjunction Λ.X ell k (WeilConjectures.exceptionalCurrentFieldCD ell k hk)
      (𝟙 X) hΛ).homEquiv K K)
    (ObjectProperty.homMk
      (((compCompositionWitnesses ell k hk Λ.X hΛ).comparison (SepFinType.homMk (𝟙 X))
          (compactificationOverField (𝟙 X)) (Compactification.ofIsProper (𝟙 X.left))).hom.app
          (condensedGraphLocalizing Λ K) ≫
        (CompactSupportComposition.identity Λ.X X.left).hom.app K.obj))

/-- The coefficient map of the graph endocorrespondence of `(h, v)`: `u = ι_{X,K} ∘ v`,
from `Lh^* K = c₂^* K` to `R(id_X)^! K = c₁^! K`. Together with `C = X`, `c₁ = id_X`, `c₂ = h`
it is the endocorrespondence fed to the graph-operator construction.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; graph `(id_X, h)` and
coefficient map `u = ι_{X,K} ∘ v`
(blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
def condensedGraphCoefficient (h : X ⟶ X) (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (v : (moduleObjectDerivedPullback Λ.X h.left).obj K.obj ⟶ K.obj) :
    (moduleObjectDerivedPullback Λ.X h.left).obj K.obj ⟶
      ((ctfExceptionalInverseImage Λ.X ell k (WeilConjectures.exceptionalCurrentFieldCD ell k hk)
        (𝟙 X) hΛ).obj K).obj :=
  v ≫ (condensedGraphIdentityUnit ell k hk Λ hΛ X K).hom

/-- The proper comparison `P₂ : Rh_! ≃ Rh_*` for the proper ordinary leg `h`: the
compactification comparison from the chosen compactification of `h` to the compactification
`X → X → X` by `(id_X, h)`, followed by `Rh_*` of the identification `(id_X)_! ≃ id`.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; proper comparison
`P₂` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
def condensedGraphProperComparison (h : X ⟶ X) [IsProper h.left]
    (L : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (rightDerivedLowerShriekOfCompactification Λ.X (compactificationOverField h)).obj L.obj ⟶
      (RootCoordinateFace.lower Λ.X h.left).obj L.obj :=
  ((compCompositionWitnesses ell k hk Λ.X hΛ).comparison (SepFinType.homMk h)
      (compactificationOverField h) (Compactification.ofIsProper h.left)).hom.app
      (condensedGraphLocalizing Λ L) ≫
    (RootCoordinateFace.lower Λ.X h.left).map
      ((derivedOpenImmersionLowerShriekId Λ.X X.left).hom.app L.obj)

/-- The compact-support composition comparison `μ : Ra_{X!} Rf_! ≃ R(a_X f)_! = Ra_{X!}` for a
`k`-endomorphism `f`, with the chosen compactifications; `f = id_X` gives `μ₁` and `f = h`
gives `μ₂` of the graph-operator composite.
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; composition
comparisons `μ₁, μ₂` (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
def condensedGraphCompositionComparison (f : X ⟶ X) :
    (localizingClosureProEtale Λ.X X.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X (compactificationOverField f) ⋙
          rightDerivedLowerShriekOfCompactification Λ.X
            (condensedGraphStructureCompactification X)) ≅
      (localizingClosureProEtale Λ.X X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ.X
          (condensedGraphCompositeCompactification X f) :=
  (compCompositionWitnesses ell k hk Λ.X hΛ).comp (SepFinType.homMk f)
    (condensedGraphStructureMap X) (compactificationOverField f)
    (condensedGraphStructureCompactification X) (condensedGraphCompositeCompactification X f)

end Construction

section GraphRestriction

private theorem graph_restricted_homEquiv
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L' ⊣ R') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    {L : C ⥤ D} {R : D ⥤ C}
    (e₁ : iC ⋙ L' ≅ L ⋙ iD) (e₂ : iD ⋙ R' ≅ R ⋙ iC)
    (K : C) (N : D) (b : L.obj K ⟶ N) :
    iC.map ((adj.restrictFullyFaithful hiC hiD e₁ e₂).homEquiv K N b) =
      adj.homEquiv (iC.obj K) (iD.obj N) (e₁.hom.app K ≫ iD.map b) ≫ e₂.hom.app N := by
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply, hiC.map_preimage,
    Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  finiteSuppliedAdjunctionData

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)
  (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]
  (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)

local instance (T : SepFinType k) :
    LocallyOfFiniteType (T.obj.left ↘ Spec (.of k)) := by
  change LocallyOfFiniteType T.obj.hom
  infer_instance

local instance (T : SepFinType k) : QuasiCompact (T.obj.left ↘ Spec (.of k)) := by
  change QuasiCompact T.obj.hom
  infer_instance

local instance (T : SepFinType k) : IsSeparated (T.obj.left ↘ Spec (.of k)) := by
  change IsSeparated T.obj.hom
  infer_instance

set_option maxHeartbeats 2000000 in
-- Restricting the chosen functors requires a larger elaboration budget.
end GraphRestriction

section FiniteSpecialization

variable (F : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]
  (hℓ : ℓ ≠ F.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ℓ ^ n) • a = 0)
  [Fact (ringChar F.k).Prime] [Fact (ringChar F.k ≠ ℓ)]
  (X : Over (Spec (.of F.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- A finite discrete coefficient ring `A` as a condensed coefficient ring
(the discrete condensed realization of `def-trf-graph-correspondence`).
Source: sk-thm-tf-uniform-formula proof, operator-identification sentence; finite coefficient
stage (blueprint: lem-trf-condensed-graph-correspondence-base-change). -/
abbrev condensedGraphFiniteRing : ScalarSixRing.{u} :=
  ⟨Profinite.continuousMapRingObj.{u} A⟩

private theorem graph_homEquiv_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (K : C) (N : D) (b : L₁.obj K ⟶ N) :
    adj₁.homEquiv K N b ≫ (conjugateEquiv adj₁ adj₂ α).app N =
      adj₂.homEquiv K N (α.app K ≫ b) := by
  rw [Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality, ← Category.assoc,
    unit_conjugateEquiv, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 2000000 in
-- The compactification and adjunction comparison needs more than the default budget.
end FiniteSpecialization

end AlgebraicGeometry.ProEtale.CondensedRing
