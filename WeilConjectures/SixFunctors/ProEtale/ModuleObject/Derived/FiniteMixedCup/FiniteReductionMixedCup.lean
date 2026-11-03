/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.PoincareDualityConventions.PoincareDualityConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
public import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteReduction.FiniteReductionData
import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
import WeilConjectures.SmoothPurity.Supporting.BasicOperationReductionAndEvaluation
import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible

/-! # Finite reduction of the native mixed-support cup

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
`thm-pod-finite-reduction.proof.md`, first paragraph, and the coefficient-compatibility
clause of `def-pod-mixed-support-cup-product.md`.
(blueprint: prop-pod-finite-reduction-mixed-cup).

The point comparison is the adjunct of the actual scalar-extension unit. The
restriction comparison is normalized on sections of the underlying abelian sheaf.
The existence of its normalized presentation is part of the conclusion, so no
coefficient comparison or compatibility is assumed.

## Main definitions

- `pointComparison`: the unit-adjunct finite-point comparison.
- `PointData`: its section, representative and coefficient-unit normalizations.
- `compactComparison`, `ordinaryComparison`: the two cohomology comparisons.
- `finiteReductionMixedCup`: preservation of the specified native cup.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Some legacy proof imports disable this existing small-localization instance.
attribute [local instance 30000] HasDerivedCategory.ofIsGrothendieckAbelian
  AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local implicit_reducible] CommMon.toMon

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteMixedCup

open AffineRestrictionLocality

/-- The scalar map on singleton sections, retaining its actual multiplication and unit.
Source: the finite-point normalization in the node
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
abbrev scalarMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') : Γ Λ.X →+* Γ Λ'.X :=
  Γ.map a.hom.hom

/-- Termwise localization of the normalized restriction/sections square, conjugated
by the exact/right-derived point comparisons. Source: the definition of eta
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
@[irreducible] def restrictionDerived {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (k : Type u) [Field k] [IsAlgClosed k]
    (ρ : Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k))) ⋙
        condensedRingCoefficientSections Λ.X (Spec (.of k)) ≅
      condensedRingCoefficientSections Λ'.X (Spec (.of k)) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (scalarMap a)) :
    (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
      a.hom.hom (Spec (.of k)))).mapDerivedCategory ⋙
        TraceCupPoint.fiber Λ.X k ≅
      TraceCupPoint.fiber Λ'.X k ⋙ ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a) :=
  Functor.isoWhiskerLeft _ (TraceCupPoint.exactComparison Λ.X k) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.isoWhiskerRight (TraceCupPoint.exactComparison Λ'.X k).symm _

/-- The canonical finite-point map, defined by the extension/restriction Hom bijection.
Thus it is the unique map with the unit-adjunct equation; no inverse is chosen.
Source: the displayed characterization of eta
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
@[irreducible] def pointComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (k : Type u) [Field k] [IsAlgClosed k]
    (ρ : Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k))) ⋙
        condensedRingCoefficientSections Λ.X (Spec (.of k)) ≅
      condensedRingCoefficientSections Λ'.X (Spec (.of k)) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (scalarMap a))
    (d : ModuleCat.OrdinaryDerivedChangeOfRings.{u + 1} (scalarMap a))
    (adj : d.F ⊣ ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a))
    (N : Ambient Λ (Spec (.of k))) :
    d.F.obj ((TraceCupPoint.fiber Λ.X k).obj N) ⟶
      (TraceCupPoint.fiber Λ'.X k).obj ((scalarSixChange a (Spec (.of k))).obj N) :=
  (adj.homEquiv _ _).symm
    ((TraceCupPoint.fiber Λ.X k).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k)))).unit.app N) ≫
      (restrictionDerived a k ρ).hom.app ((scalarSixChange a (Spec (.of k))).obj N))

/-- The actual point-unit section in the right-derived presentation. Its ordinary
normalization sends 1 to the regular module's unit section.
Source: the multiplication normalization in the node
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
@[irreducible] def pointUnit (Λ : ScalarSixRing.{u}) (k : Type u)
    [Field k] [IsAlgClosed k] :
    𝟙_ (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (Γ Λ.X))) ⟶
      (TraceCupPoint.fiber Λ.X k).obj (𝟙_ (Ambient Λ (Spec (.of k)))) :=
  (TraceCupPoint.tensorData Λ.X k).derived.ε ≫
    (TraceCupPoint.exactComparison Λ.X k).inv.app _

set_option maxHeartbeats 2000000 in
-- Elaborating the representative and unit equations uses both native derived tensors.
/-- A presentation of the specified point comparison. All fields are conclusions of
finiteReductionMixedCup, including existence and invertibility. The ordinary universal
pair retains its K-flat normalization, and the adjunction is fixed by the actual chain
unit. The restriction square is the identity on the underlying sections, expressed via
the regular-module Hom bijection. Source: the eta paragraph and coefficient-unit clause
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
structure PointData {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (k : Type u) [Field k] [IsAlgClosed k] where
  restriction : Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k))) ⋙
      condensedRingCoefficientSections Λ.X (Spec (.of k)) ≅
    condensedRingCoefficientSections Λ'.X (Spec (.of k)) ⋙
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (scalarMap a)
  restriction_sections : ∀
    (M : Mod (Sheaf (ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ'.X (Spec (.of k))))
    (x : (condensedRingCoefficientSections Λ.X (Spec (.of k))).obj
      ((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k)))).obj M)),
    Mod.regularHomAddEquiv M ((restriction.hom.app M) x) =
      Mod.regularHomAddEquiv
        ((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X)
          a.hom.hom (Spec (.of k)))).obj M) x
  ordinary : ModuleCat.OrdinaryDerivedChangeOfRings.{u + 1} (scalarMap a)
  adjunction : ordinary.F ⊣ ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a)
  ordinary_unit : ∀ P : CochainComplex (ModuleCat.{u + 1} (Γ Λ.X)) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} (Γ Λ.X)) (.up ℤ)).kFlat P →
    adjunction.unit.app (DerivedCategory.Q.{u + 1}.obj P) ≫
        (ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a)).map (ordinary.counit.app P) ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (scalarMap a)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (scalarMap a)).mapHomologicalComplex
            (.up ℤ)).obj P) =
      DerivedCategory.Q.{u + 1}.map
        (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
          (scalarMap a)).mapHomologicalComplex
          (.up ℤ)).unit.app P)
  invertible : ∀ (N : Ambient Λ (Spec (.of k))), (∃ b : ℤ, N.IsLE b) →
    IsIso (pointComparison a k restriction ordinary adjunction N)
  naturality : ∀ (N N' : Ambient Λ (Spec (.of k)))
    (_hN : ∃ b : ℤ, N.IsLE b) (_hN' : ∃ b : ℤ, N'.IsLE b) (f : N ⟶ N'),
    ordinary.F.map ((TraceCupPoint.fiber Λ.X k).map f) ≫
        pointComparison a k restriction ordinary adjunction N' =
      pointComparison a k restriction ordinary adjunction N ≫
        (TraceCupPoint.fiber Λ'.X k).map ((scalarSixChange a (Spec (.of k))).map f)
  unit_equation : ∀ (N : Ambient Λ (Spec (.of k))), (∃ b : ℤ, N.IsLE b) →
    adjunction.unit.app ((TraceCupPoint.fiber Λ.X k).obj N) ≫
        (ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a)).map
          (pointComparison a k restriction ordinary adjunction N) =
      (TraceCupPoint.fiber Λ.X k).map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k)))).unit.app N) ≫
        (restrictionDerived a k restriction).hom.app
          ((scalarSixChange a (Spec (.of k))).obj N)
  unique : ∀ (N : Ambient Λ (Spec (.of k))) (_hN : ∃ b : ℤ, N.IsLE b)
    (e : ordinary.F.obj ((TraceCupPoint.fiber Λ.X k).obj N) ⟶
      (TraceCupPoint.fiber Λ'.X k).obj ((scalarSixChange a (Spec (.of k))).obj N)),
    adjunction.unit.app ((TraceCupPoint.fiber Λ.X k).obj N) ≫
        (ModuleCat.derivedRestrictScalars.{u + 1} (scalarMap a)).map e =
      (TraceCupPoint.fiber Λ.X k).map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (Spec (.of k)))).unit.app N) ≫
        (restrictionDerived a k restriction).hom.app
          ((scalarSixChange a (Spec (.of k))).obj N) →
    e = pointComparison a k restriction ordinary adjunction N
  coefficient :
    ordinary.F.map (pointUnit Λ k) ≫
        pointComparison a k restriction ordinary adjunction (𝟙_ _) ≫
        (TraceCupPoint.fiber Λ'.X k).map
          (Functor.OplaxMonoidal.η (scalarSixChange a (Spec (.of k)))) =
      Functor.OplaxMonoidal.η ordinary.F ≫ pointUnit Λ' k

/-- Bundle the existing positive finite quotient, without altering its ring object.
Source: A_j = O_E / pi_E^j in the node
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
abbrev finiteRing (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) : ScalarSixRing.{u} :=
  ⟨DerivedNakayama.quotientRing ell E (n + 1)⟩

/-- Bundle the canonical quotient map, not an arbitrary finite-ring homomorphism.
Source: the reduction A_n to A_m in the node
(blueprint: prop-pod-finite-reduction-mixed-cup). -/
def finiteMap (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] {m n : ℕ} (h : m ≤ n) :
    finiteRing ell E n ⟶ finiteRing ell E m :=
  ⟨⟨FiniteReduction.ringMap ell E h⟩⟩

set_option maxHeartbeats 2000000 in
-- Elaborating the cup square uses the native scalar and point tensor presentations.
/-- Finite coefficient reduction preserves the specified native mixed-support cup.
The lower positive level is m+1 and the upper one is P.level, written in the
predecessor coordinates P.level-1+1. The identity reduction is included.
The point normalization, its natural invertibility and its multiplication-unit
normalization are part of PointData in the conclusion, not assumptions.

Source: latest blueprint, thm-pod-finite-reduction.proof.md, first paragraph,
with the native mixed-support definition and finite-point normalization
(blueprint: prop-pod-finite-reduction-mixed-cup).

Proof:
1. Apply lem-sf-condensed-point-derived-scalar-comparison to the two finite quotient
rings. The identity-on-sections restriction square and its termwise localization
transport its internal-module assertion to the coefficient-section coordinates.
The ordinary K-flat universal pair and its normalized adjunction supply PointData.
The adjunction Hom bijection gives the unit equation and uniqueness of pointComparison;
the point lemma gives natural invertibility on bounded-above objects. Its unit formula
is exactly multiplication 1 tensor a to a in these coordinates.
2. In the fixed compactification, lem-fix-operation-reduction preserves the proper
projection transpose, the open-support factor, and the pullback compositor. Thus the
projection square commutes for the native compact-support scalar comparison.
The counit equation of det-prop-scalar-six-direct-image identifies scalar extension
of the native counit with the reduced counit composed with the pullback comparison.
3. Apply this square to N = Ra_* L. Naturality of the projection and compact-support
comparison, followed by cancellation of the pullback comparison and its inverse,
gives the scalar square for TraceCupMixed.site. Apply exact point sections and the
monoidal equation of the point lemma, and precompose with scalar extension of the
inverse point tensor comparison. By definition this gives the two cups below and
exactly compactComparison, ordinaryComparison and the ordinary inverse tensorator.
All tensors are derived; no flatness of the quotient map is used.
-/
theorem finiteReductionMixedCup (P : WeilConjectures.PoincareDualityConventions.{u})
    (m : ℕ) (h : m ≤ P.level - 1) :
    ∃ e : PointData (finiteMap P.coefficients.l P.extension.val h) P.datum.k,
      ∀ (c : Compactification P.structureMap)
        (K L : ConstantModelConstructibleFiniteTor
          (finiteRing P.coefficients.l P.extension.val (P.level - 1)).X P.X),
      e.ordinary.F.map
          (TraceCupMixed.cup (finiteRing P.coefficients.l P.extension.val (P.level - 1))
            P.datum.k c K.obj L.obj) ≫
          compactComparison e c (K.obj ⊗ L.obj) ≫
          (condensedRingCompactCoefficientComplex
            (finiteRing P.coefficients.l P.extension.val m).X c).map
            (scalarSixTensorIso (finiteMap P.coefficients.l P.extension.val h)
              P.X K.obj L.obj).hom =
        Functor.OplaxMonoidal.δ e.ordinary.F
            ((condensedRingCompactCoefficientComplex
              (finiteRing P.coefficients.l P.extension.val (P.level - 1)).X c).obj K.obj)
            ((condensedRingOrdinaryCoefficientComplex
              (finiteRing P.coefficients.l P.extension.val (P.level - 1)).X
              P.structureMap).obj L.obj) ≫
          (compactComparison e c K.obj ⊗ₘ ordinaryComparison e P.structureMap L.obj) ≫
          TraceCupMixed.cup (finiteRing P.coefficients.l P.extension.val m)
            P.datum.k c
            ((scalarSixChange (finiteMap P.coefficients.l P.extension.val h) P.X).obj K.obj)
            ((scalarSixChange (finiteMap P.coefficients.l P.extension.val h) P.X).obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteMixedCup
