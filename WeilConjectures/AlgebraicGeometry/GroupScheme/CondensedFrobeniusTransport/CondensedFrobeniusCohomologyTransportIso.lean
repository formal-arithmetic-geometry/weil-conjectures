/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.Compactification.Over
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.ZetaWeil.FrobeniusPointTransportDirect

/-! # Canonical Frobenius transport with condensed coefficients

Source: latest blueprint, `def-weil-global-geometric-frobenius`, first arrow in each
cohomology display, and `lem-trf-frobenius-operator-compact-description`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso)

All categories are the ordinary unbounded derived categories of modules over the actual
pulled-back condensed ring. The compactification is the base change of the chosen model.
The exchange maps are the published adjunction mates, and the point insertion uses the
canonical coefficient comparison, rather than a chosen isomorphism of vector spaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedFrobeniusTransport

attribute [local instance] IsAlgClosure.isAlgClosed

variable (D : FiniteFieldDatum.{u})

/-- Spec of geometric field Frobenius, with the inverse Spec of arithmetic Frobenius.
Source: latest blueprint `def-weil-frobenius-detailed`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def pointFrobenius : Spec (.of D.k) ≅ Spec (.of D.k) :=
  letI := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]

/-- The specified compactification, obtained by base change from k₀ to k.
Source: latest blueprint, the compact-support composite.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
abbrev compactification (c₀ : Compactification Y₀.hom) :
    Compactification (D.geometricFiber Y₀).hom :=
  c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Frobenius on the middle scheme of this very compactification.
Source: latest blueprint, compact-support exchange square.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def middleFrobenius (c₀ : Compactification Y₀.hom) :
    (compactification D Y₀ c₀).Z ≅ (compactification D Y₀ c₀).Z :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap c₀.g
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap c₀.g
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse c₀.g _).1
    inv_hom_id := (D.galoisMap_inverse c₀.g _).2 }

/-- The three squares used in the specified exchanges commute.
Source: latest blueprint, first arrows of `def-weil-global-geometric-frobenius`.
(blueprint: def-weil-frobenius-cohomology-transport)
Proof: each Frobenius fixes the model projection and acts by Spec γ on the field
projection. The proper square follows directly from the second projection formula.
For the open square both composites have first projection j₀ after the model projection
and second projection Spec γ after the field projection; pullback uniqueness identifies
them. The structure square is the same second projection formula for Y₀. -/
theorem squares (c₀ : Compactification Y₀.hom) :
    CommSq (D.geometricFrobenius Y₀).hom (D.geometricFiber Y₀).hom
      (D.geometricFiber Y₀).hom (pointFrobenius D).hom ∧
    CommSq (middleFrobenius D Y₀ c₀).hom (compactification D Y₀ c₀).g
      (compactification D Y₀ c₀).g (pointFrobenius D).hom ∧
    CommSq (D.geometricFrobenius Y₀).hom (compactification D Y₀ c₀).i
      (compactification D Y₀ c₀).i (middleFrobenius D Y₀ c₀).hom := by
  let := Fintype.ofFinite D.k₀
  let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  refine ⟨⟨(D.galoisMap_projections Y₀.hom σ).2⟩,
    ⟨(D.galoisMap_projections c₀.g σ).2⟩, ⟨?_⟩⟩
  change D.galoisMap Y₀.hom σ ≫
      (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).i =
    (c₀.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).i ≫
      D.galoisMap c₀.g σ
  apply pullback.hom_ext
  · simp only [Compactification.baseChange_i_fst, Category.assoc]
    erw [← Category.assoc, (D.galoisMap_projections Y₀.hom σ).1,
      (D.galoisMap_projections c₀.g σ).1, Compactification.baseChange_i_fst]
  · simp only [Compactification.baseChange_i_snd, Category.assoc]
    erw [(D.galoisMap_projections Y₀.hom σ).2,
      (D.galoisMap_projections c₀.g σ).2, ← Category.assoc,
      Compactification.baseChange_i_snd]

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- Exact point evaluation with restriction along the recorded scalar-section map,
derived on the ordinary module categories. Its scalar ring ΓΛ is canonically Λ(*).
Source: latest blueprint, `def-weil-ordinary-compact-cohomology`.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
abbrev pointSections := (condensedRingCoefficientSections Λ.X (Spec (.of D.k))).rightDerivedFunctor

/-- Restriction N(s,1) → N(s,g_s) with the canonical coefficient identification.
The point-pullback equivalence and its composition comparison normalize this map:
`upperStarIsoIdOfIsSepClosed` is the inverse restriction. Exact pullback identifies
its derived functor with termwise pullback; whiskering gives the map on point sections.
Source: latest blueprint, the first arrow before the Weil structure is applied.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def insertion : pointSections D Λ ≅
    moduleObjectDerivedPullback Λ.X (pointFrobenius D).hom ⋙ pointSections D Λ :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X (pointFrobenius D).hom ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarIsoIdOfIsSepClosed Λ.X (pointFrobenius D).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- The canonical ordinary adjunction mate, with no supplied comparison map.
Source: latest blueprint, the ordinary cohomology transport composite.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def ordinaryExchange (c₀ : Compactification Y₀.hom) :=
  FrobeniusSquareExchange.direct Λ (D.geometricFiber Y₀).hom
    (squares D Y₀ c₀).1

/-- Natural ordinary transport Γ_s(e_*) after insertion along g_s.
Source: latest blueprint, first arrow in the ordinary display.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def ordinaryTransport (c₀ : Compactification Y₀.hom) :
    condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom ⟶
      moduleObjectDerivedPullback Λ.X (D.geometricFrobenius Y₀).hom ⋙
        condensedRingOrdinaryCoefficientComplex Λ.X (D.geometricFiber Y₀).hom :=
  Functor.whiskerLeft (moduleObjectDerivedPushforward Λ.X (D.geometricFiber Y₀).hom)
      (insertion D Λ).hom ≫
    Functor.whiskerRight (ordinaryExchange D Y₀ Λ c₀) (pointSections D Λ)

/-- Natural compact transport Γ_s(e_!) after insertion along g_s, for the fixed c.
Source: latest blueprint, first arrow in the compact-support display.
(blueprint: lem-weil-frobenius-cohomology-transport-iso) -/
def compactTransport (c₀ : Compactification Y₀.hom) :
    condensedRingCompactCoefficientComplex Λ.X (compactification D Y₀ c₀) ⟶
      moduleObjectDerivedPullback Λ.X (D.geometricFrobenius Y₀).hom ⋙
        condensedRingCompactCoefficientComplex Λ.X (compactification D Y₀ c₀) :=
  Functor.whiskerLeft
      (rightDerivedLowerShriekOfCompactification Λ.X (compactification D Y₀ c₀))
      (insertion D Λ).hom ≫
    Functor.whiskerRight (compactExchange D Y₀ Λ c₀) (pointSections D Λ)

end WeilConjectures.CondensedFrobeniusTransport
