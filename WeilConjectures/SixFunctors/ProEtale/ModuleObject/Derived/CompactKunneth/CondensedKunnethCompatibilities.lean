/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.SixFunctors.FiniteFieldDatum.SchemeFrobeniusGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.SixFunctors.CompactSupportPbcTransport.CompactSupportProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization

/-! # Native condensed compact-support Künneth compatibilities

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/
sk-lem-wft-compact-kunneth/lem-wft-kunneth-compatibilities.md, clauses (1)--(3)
(blueprint: lem-wft-kunneth-compatibilities).

The forward map uses only the specified proper/open projection morphisms, compact-support
exchange and compositor. Its inverse is therefore fixed, including the coordinate convention.
The finite-Tor objects used below are exactly Dbc at the two field coefficients, by
integral_ctf_equals_bc. All tensor symmetries are the named derived Koszul symmetries.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunneth

variable (ell : ℕ) [Fact ell.Prime]

/-- The two native field coefficient presentations in the statement.
Source: clause (1), coefficient convention (blueprint: lem-wft-kunneth-compatibilities). -/
def FieldCoefficient (c : Coefficient ell) : Prop :=
  (∃ E : PadicAlgCl.FiniteIntermediateField ell, c = .rational E) ∨ c = .closure

variable {ell}

/-- The actual Koszul symmetry, with no unspecified braiding instance.
Source: clause (1), sigma (blueprint: lem-wft-kunneth-compatibilities). -/
def symmetry (c : Coefficient ell) (X : Scheme.{u}) (K L : c.derived ell X) :
    K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K L

/-- External product in the ordinary module-object derived category.
Source: clause (1), definition of boxtimes (blueprint: lem-wft-kunneth-compatibilities). -/
def external (c : Coefficient ell) {T X Y : Scheme.{u}} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.derived ell X) (L : c.derived ell Y) : c.derived ell T :=
  (moduleObjectDerivedPullback (c.obj ell) u).obj K ⊗
    (moduleObjectDerivedPullback (c.obj ell) v).obj L

/-- Pullback and tensor preserve the stated finite-Tor constructible domain.
Source: clause (1), domain check (blueprint: lem-wft-kunneth-compatibilities).
Proof: apply det-thm-sf-ctf-stability-direct-images to each pullback and to tensor.
The two finite Tor intervals add under tensor. This is step 1 of the node's proof. -/
theorem external_mem (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    {T X Y : SepFinType D.k} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.ctf ell X.obj.left) (L : c.ctf ell Y.obj.left) :
    property ell c T.obj.left (external c u.hom.left v.hom.left K.obj L.obj) := by
  sorry

/-- The same external product as an object of the existing Dctf full subcategory.
Source: clause (1), constructible domain (blueprint: lem-wft-kunneth-compatibilities). -/
def externalCtf (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    {T X Y : SepFinType D.k} (u : T ⟶ X) (v : T ⟶ Y)
    (K : c.ctf ell X.obj.left) (L : c.ctf ell Y.obj.left) : c.ctf ell T.obj.left :=
  ⟨external c u.hom.left v.hom.left K.obj L.obj, external_mem D c H u v K L⟩

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {c : Coefficient ell}
  (Q : Square ell D c)

/-- The canonical beta, oriented from a* Rb! to Ru! v*.
Source: clause (1), beta_L (blueprint: lem-wft-kunneth-compatibilities). -/
def beta (L : c.ctf ell Q.Y.obj.left) :
    (moduleObjectDerivedPullback (c.obj ell) Q.a.hom.left).obj
        ((rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj) ≅
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cu).obj
        ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) :=
  (Q.coherent.exchange Q.cartesian Q.cb Q.cu).app ((inclusion ell c _).obj L)

/-- The forward Künneth map: projection for a, beta, coefficient-first projection for u,
and the normalized compositor. Its inverse is precisely the displayed kappa.
Source: clause (1), four-arrow composite (blueprint: lem-wft-kunneth-compatibilities). -/
def forward (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).obj K.obj ⊗
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj ⟶
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).obj
        (external c Q.u.hom.left Q.v.hom.left K.obj L.obj) :=
  exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.ca K.obj _ ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      (K.obj ◁ (beta Q L).hom) ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      ((symmetry c Q.X.obj.left K.obj _).hom ≫
        exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.cu
          ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) K.obj ≫
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cu).map
          (symmetry c Q.W.obj.left _ _).hom) ≫
    (Q.coherent.comp Q.u Q.a Q.cu Q.ca Q.cc).hom.app
      ((inclusion ell c _).obj (externalCtf D c Q.coherent Q.u Q.v K L))

/-- The inverse-direction version of the relative recipe, with its independent middle
symmetry and ordered pair (b,L),(a,K), rather than a definition by conjugating kappa.
Source: clause (1), r_{L,K} recipe (blueprint: lem-wft-kunneth-compatibilities). -/
def relativeForward (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cb).obj L.obj ⊗
        (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).obj K.obj ⟶
      (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.cc).obj
        (external c Q.v.hom.left Q.u.hom.left L.obj K.obj) :=
  (symmetry c Q.S.obj.left _ _).hom ≫
    exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.ca K.obj _ ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      ((symmetry c Q.X.obj.left _ _).hom ≫ (beta Q L).hom ▷ K.obj) ≫
    (rightDerivedLowerShriekOfCompactification (c.obj ell) Q.ca).map
      (exceptionalProjectionMorphismOfCompactification (c.obj ell) Q.cu
        ((moduleObjectDerivedPullback (c.obj ell) Q.v.hom.left).obj L.obj) K.obj) ≫
    (Q.coherent.comp Q.u Q.a Q.cu Q.ca Q.cc).hom.app
      ((inclusion ell c _).obj (externalCtf D c Q.coherent Q.v Q.u L K))

/-- Both canonical forward maps are invertible on exactly the stated field domain.
Source: clause (1) (blueprint: lem-wft-kunneth-compatibilities).
Proof: by lem-integral-ctf-equals-bc this is the entire Dbc field domain. In step 1,
pullback, tensor and compact support preserve Dctf. Step 2 applies
fix-prop-projection-formula to a and u and det-prop-sf-cbc to the Cartesian square.
Each factor is an isomorphism; the compositor is sk-thm-sf-comp-composition. -/
theorem forward_isIso (_hEll : ell ≠ D.p) (_hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :
    IsIso (forward Q K L) ∧ IsIso (relativeForward Q K L) := by
  sorry

/-- The native relative Künneth recipe, as the unique inverse of relativeForward.
Source: clause (1), r_{L,K} (blueprint: lem-wft-kunneth-compatibilities). -/
def relative (hEll : ell ≠ D.p) (hc : FieldCoefficient ell c)
    (K : c.ctf ell Q.X.obj.left) (L : c.ctf ell Q.Y.obj.left) :=
  letI := (forward_isIso Q hEll hc K L).2
  (asIso (relativeForward Q K L)).symm

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunneth
