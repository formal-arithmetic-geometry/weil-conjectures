/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TensorHomExchangeCore
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension

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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Invertibility of the exceptional shift mate

The exceptional shift is determined by the native compact-support shift and
its exceptional counit. Source: `sk-thm-sf-tensor-hom`, Complement
(blueprint: lem-sf-exceptional-shift-mate-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory

private theorem shift_mate_isIso {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D} {G : D ⥤ C}
    [F.CommShift ℤ] (adj : F ⊣ G) (Y : D) (n : ℤ) :
    IsIso (adj.homEquiv _ _
      ((F.commShiftIso n).hom.app (G.obj Y) ≫ (adj.counit.app Y) ⟦n⟧')) := by
  let := adj.rightAdjointCommShift ℤ
  have h := Adjunction.CommShift.compatibilityUnit_right adj (F.commShiftIso n)
    (G.commShiftIso n) (Adjunction.RightAdjointCommShift.compatibilityUnit_iso adj n) Y
  have he : adj.homEquiv _ _
      ((F.commShiftIso n).hom.app (G.obj Y) ≫ (adj.counit.app Y) ⟦n⟧') =
      (G.commShiftIso n).inv.app Y := by
    rw [adj.homEquiv_unit, Functor.map_comp]
    exact h.symm
  rw [he]
  infer_instance

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

namespace AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalRingTransport

set_option maxHeartbeats 1200000 in
-- Comparing restricted native shifts unfolds large derived-functor expressions.
/-- The counit-defined exceptional shift mate is invertible, for every coefficient
ring and every integer shift.

Source: `sk-thm-sf-tensor-hom`, Complement, and adjunction-compatible uniqueness
of right-adjoint shifts (blueprint: lem-sf-exceptional-shift-mate-invertible).

Proof: thickness makes both finite-Tor constructible properties shift-stable.
Restrict the native compact-support shift to their full subcategories. Mathlib
constructs the compatible shift on its right adjoint; its inverse component is
the exceptional transpose of the native left shift followed by the shifted
counit. This is precisely exceptionalShift. Full faithfulness of the inclusion
identifies the components and preserves their invertibility. -/
theorem exceptionalShift_isIso (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k) (Λ : ScalarSixRing.{u})
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (L : ConstantModelConstructibleFiniteTor Λ.X Y.left) (n : ℤ) :
    IsIso (exceptionalShift ℓ k hcd Λ hΛ f L n) := by
  let := (sfbAdmissibleConstructibleThickness ℓ Λ hΛ k X).1
  let := (sfbAdmissibleConstructibleThickness ℓ Λ hΛ k Y).1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.2.2.2.2.2.2.1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ.X Y.left).2.2.2.2.2.2.2.1
  let F := ctfLowerShriek Λ.X ℓ k hcd f hΛ
  let G := ctfExceptionalInverseImage Λ.X ℓ k hcd f hΛ
  let adj := ctfExceptionalAdjunction Λ.X ℓ k hcd f hΛ
  let : F.CommShift ℤ := by
    dsimp [F, ctfLowerShriek]
    infer_instance
  let := shift_mate_isIso adj L n
  have hm := Functor.map_isIso
    (ObjectProperty.ι (constantModelBoundedConstructible Λ.X X.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _))
    (adj.homEquiv _ _
      ((F.commShiftIso n).hom.app (G.obj L) ≫ (adj.counit.app L) ⟦n⟧'))
  have hf (A : ConstantModelConstructibleFiniteTor Λ.X X.left) :
      ((F.commShiftIso n).hom.app A).hom =
        ((rightDerivedLowerShriekOfCompactification Λ.X
          (compactificationOverField f)).commShiftIso n).hom.app A.obj := by
    let e : F ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ rightDerivedLowerShriekOfCompactification Λ.X
          (compactificationOverField f) := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    change (ObjectProperty.ι _).map ((Functor.CommShift.OfComp.iso e n).hom.app A) = _
    rw [Functor.CommShift.OfComp.map_iso_hom_app]
    have hιX : ((ObjectProperty.ι (constantModelBoundedConstructible Λ.X X.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)).commShiftIso n).hom.app A =
        𝟙 (A.obj ⟦n⟧) := by
      unfold ObjectProperty.commShiftι
      rfl
    have hιY : ((ObjectProperty.ι (constantModelBoundedConstructible Λ.X Y.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)).commShiftIso n).inv.app (F.obj A) =
        𝟙 ((F.obj A).obj ⟦n⟧) := by
      unfold ObjectProperty.commShiftι
      rfl
    simp only [Functor.commShiftIso_comp_hom_app, hιX, hιY]
    dsimp only [e, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      Iso.refl_hom, Iso.refl_inv, Functor.comp_obj, ObjectProperty.ι_obj]
    dsimp only [F, ctfLowerShriek, ObjectProperty.lift, Functor.comp_obj,
      ObjectProperty.ι_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact (congrArg (fun z ↦ z ≫ _)
      ((rightDerivedLowerShriekOfCompactification Λ.X
        (compactificationOverField f)).map_id (A.obj ⟦n⟧))).trans (Category.id_comp _)
  have hshiftX : (G.obj L) ⟦n⟧ = shiftObject ℓ k Λ hΛ X (G.obj L) n := by
    unfold shiftObject
    rfl
  have hshiftY : L⟦n⟧ = shiftObject ℓ k Λ hΛ Y L n := by
    unfold shiftObject
    rfl
  have hi : ((F.commShiftIso n).hom.app (G.obj L) ≫ (adj.counit.app L) ⟦n⟧') =
      ObjectProperty.homMk
        (((rightDerivedLowerShriekOfCompactification Λ.X
          (compactificationOverField f)).commShiftIso n).hom.app (G.obj L).obj ≫
          ((adj.counit.app L).hom) ⟦n⟧') := by
    apply ObjectProperty.hom_ext
    change ((F.commShiftIso n).hom.app (G.obj L)).hom ≫
      ((shiftFunctor _ n).map (adj.counit.app L)).hom = _
    rw [hf]
    rfl
  rw [hi] at hm
  change IsIso ((adj.homEquiv ((G.obj L) ⟦n⟧) (L ⟦n⟧)
    (ObjectProperty.homMk
      (((rightDerivedLowerShriekOfCompactification Λ.X
        (compactificationOverField f)).commShiftIso n).hom.app (G.obj L).obj ≫
        ((adj.counit.app L).hom) ⟦n⟧'))).hom) at hm
  exact hm

end AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalRingTransport
