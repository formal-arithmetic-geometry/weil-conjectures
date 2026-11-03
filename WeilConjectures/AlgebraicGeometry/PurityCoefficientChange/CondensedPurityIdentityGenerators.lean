/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityScalarCoordinates

/-! # Identity generators and changes of coefficient presentation

Source: identity clause of the coefficient-change proof, Step 9.
(blueprint: lem-pur-condensed-coefficient-identity-generators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityCoefficientChange
open PurityTransport

/-- Adding identities to the composition-closed generating list adds only equality
transports. Source: successive-change convention in coefficient-change Step 9
(blueprint: lem-pur-condensed-coefficient-identity-generators).
Proof: induct on the closure proof. Two generating arrows compose to a generating
arrow. In either remaining case eliminate the equality of endpoints and simplify
the composition with the identity. -/
theorem listed_scalar_normal_form (ell : ℕ) [Fact ell.Prime]
    {Λ Λ' : ScalarSixRing.{u}} {a : Λ ⟶ Λ'} (ha : ListedScalarChange ell a) :
    IsListedScalarCoefficientMap ell a ∨ ∃ h : Λ = Λ', a = eqToHom h := by
  induction ha with
  | ofListed ha => exact Or.inl ha
  | identity Λ hΛ => exact Or.inr ⟨rfl, rfl⟩
  | comp a b ha hb ih ih' =>
    rcases ih with h | ⟨e, h⟩
    · rcases ih' with h' | ⟨e', h'⟩
      · exact Or.inl (.comp h h')
      · cases e'
        subst b
        simpa only [eqToHom_refl, Category.comp_id] using Or.inl h
    · cases e
      subst a
      simpa only [eqToHom_refl, Category.id_comp] using ih'

private theorem integralMap_refl (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    latticeIntegralMap.{u} ell (le_refl E) = 𝟙 _ := by
  rfl

private theorem fieldMap_refl (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (⟨⟨Profinite.padicSubfieldRingObjMap ell (le_refl E)⟩⟩ :
      scalarSixFieldRing.{u} ell E ⟶ scalarSixFieldRing ell E) =
      𝟙 (scalarSixFieldRing.{u} ell E) := by
  apply CommMon.hom_ext
  exact Profinite.padicSubfieldRingObjMap_id ell E

private theorem continuousMap_id {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    scalarSixContinuousMap.{u} (RingHom.id A) continuous_id = 𝟙 _ := by
  apply CommMon.hom_ext
  change (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap (RingHom.id A) continuous_id) = _
  rw [Profinite.continuousMapRingSheafMap_id]
  exact CategoryTheory.Functor.map_id _ _

private def continuousRingIso {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    scalarSixTopologicalRing.{u} A ≅ scalarSixTopologicalRing B where
  hom := scalarSixContinuousMap e.toRingHom he
  inv := scalarSixContinuousMap e.symm.toRingHom hi
  hom_inv_id := by
    ext S f
    apply ULift.ext
    ext x
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext S f
    apply ULift.ext
    ext x
    exact e.apply_symm_apply _

private def bottomFieldIso (ell : ℕ) [Fact ell.Prime] :
    scalarSixTopologicalRing.{u} ℚ_[ell] ≅
      scalarSixFieldRing ell (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ell) := by
  let E : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  let e := (IntermediateField.botEquiv ℚ_[ell] (PadicAlgCl ell)).symm
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm
    intro x
    change ‖algebraMap ℚ_[ell] (PadicAlgCl ell) x‖ = ‖x‖
    exact PadicAlgCl.norm_extends ell x
  exact continuousRingIso e.toRingEquiv he.continuous (show Continuous e.symm from
    ({ toEquiv := e.toEquiv, isometry_toFun := he } : ℚ_[ell] ≃ᵢ E).symm.continuous)

private def bottomIntegerIso (ell : ℕ) [Fact ell.Prime] :
    scalarSixTopologicalRing.{u} ℤ_[ell] ≅
      latticeIntegralRing ell (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ell) := by
  let E : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  let f := ProEtale.padicIntToIntegers ell E.1
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply FaithfulSMul.algebraMap_injective ℚ_[ell] (PadicAlgCl ell)
      exact congrArg (fun z : PadicAlgCl.integers ell E.1 ↦
        algebraMap E.1 (PadicAlgCl ell) z) h
    · intro r
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 (r : E.1).2
      have hr := r.2
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe, coe_nnnorm] at hr
      have hq1 : ‖q‖ ≤ 1 := by
        rw [← PadicAlgCl.norm_extends ell q]
        exact hq ▸ hr
      refine ⟨⟨q, hq1⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hq
  let e := RingEquiv.ofBijective f hf
  have he : Continuous e := ProEtale.continuous_padicIntToIntegers ell E.1
  have hi : Continuous e.symm :=
    (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  exact continuousRingIso e he hi

/-- Every concrete coefficient other than the algebraic closure has a generating
identity map. Source: identity clause of coefficient-change Step 9
(blueprint: lem-pur-condensed-coefficient-identity-generators).
Proof: the finite case is the finite-map generator. Integral and finite-field
coefficients use the reflexive inclusion generator. Identify Z_ell and Q_ell with
the integers and field of the bottom finite intermediate extension; their
continuous ring isomorphisms transport the corresponding reflexive generators. -/
theorem listed_identity_of_nonclosure (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) (hc : c ≠ .closure) :
    IsListedScalarCoefficientMap ell (𝟙 (c.bundled.{u} ell)) := by
  cases c with
  | finite A fin n hA =>
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    change IsListedScalarCoefficientMap ell (𝟙 (scalarSixTopologicalRing.{u} A))
    have hA' : (ell : A) ^ (n + 1) = 0 := by
      simpa only [Nat.cast_pow] using hA
    have h := IsListedScalarCoefficientMap.finite (ell := ell)
      (n + 1) (n + 1) hA' hA' (RingHom.id A) continuous_id
    simpa only [continuousMap_id] using h
  | integers =>
    change IsListedScalarCoefficientMap ell
      (𝟙 (scalarSixTopologicalRing.{u} ℤ_[ell]))
    let e := bottomIntegerIso.{u} ell
    have h := IsListedScalarCoefficientMap.integral (ell := ell)
      (E := (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ell)) le_rfl
    have h' := IsListedScalarCoefficientMap.iso e e.symm h
    simpa only [integralMap_refl, Category.id_comp, Iso.symm_hom, Iso.hom_inv_id] using h'
  | rationals =>
    change IsListedScalarCoefficientMap ell
      (𝟙 (scalarSixTopologicalRing.{u} ℚ_[ell]))
    let e := bottomFieldIso.{u} ell
    have h := IsListedScalarCoefficientMap.field (ell := ell)
      (E := (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ell)) le_rfl
    have h' := IsListedScalarCoefficientMap.iso e e.symm h
    simpa only [fieldMap_refl, Category.id_comp, Iso.symm_hom, Iso.hom_inv_id] using h'
  | integral E =>
    change IsListedScalarCoefficientMap ell (𝟙 (latticeIntegralRing.{u} ell E))
    have h := IsListedScalarCoefficientMap.integral (ell := ell) (E := E) le_rfl
    simpa only [integralMap_refl] using h
  | rational E =>
    change IsListedScalarCoefficientMap ell (𝟙 (scalarSixFieldRing.{u} ell E))
    have h := IsListedScalarCoefficientMap.field (ell := ell) (E := E) le_rfl
    simpa only [fieldMap_refl] using h
  | closure => exact False.elim (hc rfl)

/-- An equality between distinct coefficient presentations is already a generating
listed map. Source: isomorphism-of-presentations rule in coefficient-change Step 9
(blueprint: lem-pur-condensed-coefficient-identity-generators).
Proof: at least one presentation is not the closure. Its identity is generating
by the preceding theorem. Transport the source or target along the given equality
and use the isomorphism rule of the listed-map predicate. -/
theorem listed_of_distinct_presentation (ell : ℕ) [Fact ell.Prime]
    (c c' : Coefficient ell) (hc : c ≠ c')
    (e : c.bundled.{u} ell = c'.bundled ell) :
    IsListedScalarCoefficientMap ell (eqToHom e) := by
  classical
  by_cases h : c = .closure
  · have h' : c' ≠ .closure := fun h' ↦ hc (h.trans h'.symm)
    have hh := IsListedScalarCoefficientMap.iso (eqToIso e) (Iso.refl _)
      (listed_identity_of_nonclosure ell c' h')
    simpa only [Iso.refl_hom, Category.comp_id, eqToIso.hom] using hh
  · have hh := IsListedScalarCoefficientMap.iso (Iso.refl _) (eqToIso e)
      (listed_identity_of_nonclosure ell c h)
    simpa only [Iso.refl_hom, Category.id_comp, eqToIso.hom] using hh

/-- Scalar compatibility supplies the integral-map compatibility for every map
in the reflexive closure, so normalized coefficient coordinates exist.
Source: coefficient-change proof Steps 5 and 7
(blueprint: lem-pur-condensed-coefficient-identity-generators).
Proof: put a listed change into the preceding normal form. On a generating map
use the integral equality contained in ScalarCompatible. An equality transport
between distinct presentations is generating by the preceding theorem. On a
single presentation it is the identity, whose integral equality is functoriality.
Choose the proven unique normalized line-coordinate record at every site. -/
theorem coordinates_nonempty_of_scalarCompatible (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (A : AdjunctionFamily ell D)
    (hA : ScalarCompatible ell D A) : Nonempty (Coordinates.{u} ell) := by
  classical
  have hi : ∀ {c c' : Coefficient ell}
      (a : c.bundled.{u} ell ⟶ c'.bundled ell), ListedScalarChange ell a →
      c.integralMap ell ≫ a.hom.hom = c'.integralMap ell := by
    intro c c' a ha
    rcases listed_scalar_normal_form ell ha with h | ⟨e, h⟩
    · exact (hA c c' a h).choose
    · subst a
      by_cases hc : c = c'
      · subst c'
        simp only [eqToHom_refl, CommMon.id_hom, Category.comp_id]
      · exact (hA c c' (eqToHom e) (listed_of_distinct_presentation ell c c' hc e)).choose
  refine ⟨{ integral := hi, line := ?_ }⟩
  intro c c' a ha X
  exact Classical.choice (scalarLineCoordinates_nonempty ell a (hi a ha) X)

end AlgebraicGeometry.ProEtale.PurityCoefficientChange
