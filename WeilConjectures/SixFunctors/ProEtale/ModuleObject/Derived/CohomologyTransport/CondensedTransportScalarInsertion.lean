/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Scalar naturality of normalized point insertion
Source: current uniform trace-formula proof, final coefficient-compatibility paragraph.
(blueprint: lem-trf-condensed-transport-scalar-insertion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj MonoidalCategory TensorProduct
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- Identity normalization uniquely determines the section comparison.
Source: sectionwise equality of module morphisms
(blueprint: lem-trf-condensed-transport-scalar-insertion). -/
theorem transportScalarSections_unique {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] (P Q : TransportScalarSections a k) : P = Q := by
  have hh : P.restriction.hom = Q.restriction.hom := by
    ext N x
    exact eq_of_heq ((P.normalized N x).trans (Q.normalized N x).symm)
  have h : P.restriction = Q.restriction := Iso.ext hh
  cases P
  cases Q
  cases h
  rfl

/-- Pullback from the point preserves the actual terminal coefficient map.
Source: naturality of global elements under a monoidal functor
(blueprint: lem-trf-condensed-transport-scalar-insertion). -/
theorem transportScalarMap_naturality {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (T : Scheme.{u}) (r : condensedScalarRing A.X) :
    (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom T).hom.app
        (Opposite.op (ProEt.mk (𝟙 T))) (scalarMap A.X T r) =
      scalarMap B.X T (transportScalarMap a r) := by
  have : PreservesFiniteLimits (upperStarFromPoint T) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint T).Additive :=
    Functor.additive_of_preserves_binary_products (upperStarFromPoint T)
  let eA := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) A.X (⊤_ Profinite.{u}) terminalIsTerminal
  let eB := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) B.X (⊤_ Profinite.{u}) terminalIsTerminal
  let p := eA.symm r
  have hEval₀ (s : MonObj.Γ A.X) :
      (a.hom.hom.hom.app (Opposite.op (⊤_ Profinite.{u}))) (eA s) =
        eB (MonObj.Γ.map a.hom.hom s) := by
    rfl
  have h₀ : eB.symm (transportScalarMap a r) = MonObj.Γ.map a.hom.hom p := by
    apply eB.injective
    rw [RingEquiv.apply_symm_apply]
    rw [← hEval₀]
    simp only [p, RingEquiv.apply_symm_apply]
    rfl
  have hF : MonObj.Γ.mapFunctor (upperStarFromPoint T) (MonObj.Γ.map a.hom.hom p) =
      MonObj.Γ.map (coefficientMap a.hom.hom T)
        (MonObj.Γ.mapFunctor (upperStarFromPoint T) p) := by
    ext
    simp only [MonObj.Γ.mapFunctor_hom, MonObj.Γ.map_hom, Functor.map_comp,
      Category.assoc]
  change _ = InternalAbelianSheafModule.sectionGlobalEval.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj B.X T) (ProEt.mk (𝟙 T))
    (MonObj.Γ.mapFunctor (upperStarFromPoint T) (eB.symm (transportScalarMap a r)))
  rw [h₀]
  erw [hF]
  rfl

/-- The section restriction comparison is the identity on underlying sections.
Source: naturality of the tensor action and final-object coefficient evaluation
(blueprint: lem-trf-condensed-transport-scalar-insertion). -/
def transportScalarRestrictionSections {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (T : Scheme.{u}) :
    Mod.comap (coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom T) ⋙ sections A.X T ≅
      sections B.X T ⋙ ModuleCat.restrictScalars.{u + 1} (transportScalarMap a) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext x
    let J := ProEt.topology T
    let U := Opposite.op (ProEt.mk (𝟙 T))
    let α := coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom T
    have hact (s : (condensedRingObj A.X T).obj.obj U) :
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1})
            (condensedRingObj A.X T) N.X).app U) ≫
          ((α ▷ N.X).hom.app U) ≫ ((Mod.act N.X).hom.app U)) (s ⊗ₜ[ℤ] x) =
        (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1})
            (condensedRingObj B.X T) N.X).app U) ≫
          ((Mod.act N.X).hom.app U)) ((α.hom.app U s) ⊗ₜ[ℤ] x) := by
      have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
        (sheafToPresheaf J AddCommGrpCat.{u + 1}) α N.X) U
      exact (ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f ≫ (Mod.act N.X).hom.app U) hμ) (s ⊗ₜ[ℤ] x)).symm
    change _ = (((Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{u + 1})
            (condensedRingObj A.X T) N.X).app U) ≫
          ((α ▷ N.X).hom.app U) ≫ ((Mod.act N.X).hom.app U))
        (scalarMap A.X T r ⊗ₜ[ℤ] x)
    rw [hact]
    rw [transportScalarMap_naturality]
    rfl
  · intro N N' f
    ext x
    rfl

/-- Construct the normalized point comparison without selecting any witness.
Source: identity of underlying sections under coefficient restriction
(blueprint: lem-trf-condensed-transport-scalar-insertion). -/
def transportScalarSectionsData {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] : TransportScalarSections a k where
  restriction := transportScalarRestrictionSections a (Spec (.of k))
  normalized := fun _N _x ↦ HEq.rfl

/-- The scalar square for the actual point insertion, for a normalized section comparison.
The comparison is normalized on all module sections, hence is uniquely determined.
Source: uniform formula proof, pullbacks commute with coefficient comparisons.
(blueprint: lem-trf-condensed-transport-scalar-insertion). -/
structure TransportScalarInsertion {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {k : Type u} [Field k] [IsAlgClosed k] (P : TransportScalarSections a k) : Prop where
  insertion : ∀ (b : Spec (.of k) ≅ Spec (.of k)) (N : D A.X (Spec (.of k))),
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (transportScalarMap a)).leftDerivedFunctor.map
        ((CohomologyTransport.insertion A.X b.hom).hom.app N) ≫
        (P.comparison a).app ((L A.X b.hom).obj N) ≫
        (Γ B.X (Spec (.of k))).map ((transportScalarPull a b.hom).app N) =
      (P.comparison a).app N ≫
        (CohomologyTransport.insertion B.X b.hom).hom.app
          ((scalarSixChange a (Spec (.of k))).obj N)

/-- Scalar pullback respects the specified trivialization at an algebraically closed point.
Source: naturality in the coefficient ring of pullback from the point.
(blueprint: lem-trf-condensed-transport-scalar-insertion).

Proof: the equivalence upperStarFromPointMod identifies pullback along b with the
identity using upperStarFromPointModComp. Coefficient restriction commutes with the
point functor and this compositor: both maps use the same underlying pullback, and
naturality of the coefficient identification alpha_b identifies their ring maps.
Precompose with the point equivalence to check the restriction square, cancel its
unit/counit, and use full faithfulness to descend it to all internal modules. Derive
this exact square termwise. The exact-to-total pullback comparison identifies the
resulting trivializations with the displayed composites. Taking mates through the
specified extension/restriction adjunctions gives scalarSixPullHom. Whisker with the
exact-to-total comparisons and cancel them to obtain transportScalarPull and the
stated equation. This is an internal-module equation before point sections.
-/
theorem condensedTransportScalarPointTrivialization
    {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ≅ Spec (.of k)) (N : D A.X (Spec (.of k))) :
    (scalarSixChange a (Spec (.of k))).map
        ((leftDerivedUpperStarIsoMapDerivedCategory A.X b.hom ≪≫
          Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed A.X b.hom) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv.app N) ≫
        (transportScalarPull a b.hom).app N =
      (leftDerivedUpperStarIsoMapDerivedCategory B.X b.hom ≪≫
        Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed B.X b.hom) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv.app
          ((scalarSixChange a (Spec (.of k))).obj N) := by
  sorry

/-- The cohomological insertion square follows from the internal point square by naturality.
It holds for every normalized section comparison, not just the constructed one.
Source: naturality of the specified scalar cohomology comparison.
(blueprint: lem-trf-condensed-transport-scalar-insertion).

Proof: insertion is point sections of the inverse internal trivialization. Naturality
of P.comparison moves this inverse trivialization past the scalar comparison. Functoriality
of point sections and the internal point square then give exactly the B insertion.
-/
theorem condensedTransportScalarInsertion {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (k : Type u) [Field k] [IsAlgClosed k] (P : TransportScalarSections a k) :
    TransportScalarInsertion a P := by
  constructor
  intro b N
  let κ := (leftDerivedUpperStarIsoMapDerivedCategory A.X b.hom ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed A.X b.hom) ≪≫
    Functor.mapDerivedCategoryIdIso _).inv.app N
  have hn := (P.comparison a).naturality κ
  have hp := condensedTransportScalarPointTrivialization a k b N
  simp only [CohomologyTransport.insertion, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp]
  change (ModuleCat.extendScalars (transportScalarMap a)).leftDerivedFunctor.map
      ((Γ A.X (Spec (.of k))).map κ) ≫
      (P.comparison a).app ((L A.X b.hom).obj N) ≫
      (Γ B.X (Spec (.of k))).map ((transportScalarPull a b.hom).app N) = _
  dsimp only [L, moduleObjectDerivedPullback, Functor.comp_map, Functor.id_obj] at *
  rw [reassoc_of% hn, ← (Γ B.X (Spec (.of k))).map_comp, hp]

end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
