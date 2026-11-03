/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction
import WeilConjectures.SixFunctors.Compact.CompactSupportReductionCoherence
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefEtaleRelativeTraceRestriction
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefSupportRealizationRestriction
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Compactification.Over
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
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

/-! # Quotient compatibility of the prescribed intrinsic finite trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

private theorem map_insert_inv_hom
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {w v : D} (a : x ⟶ y) (e : z ≅ y)
    (b : F.obj y ⟶ w) (q : w ⟶ v) :
    (F.map a ≫ b) ≫ q = F.map (a ≫ e.inv) ≫ (F.map e.hom ≫ b ≫ q) := by
  simp only [Functor.map_comp, Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

private theorem paste_trace_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x xr x0 : C} {s1 sr sR s0 y1 yR y0 : D}
    (eX : x0 ≅ xr) (eS : s0 ≅ sR) (eY : y0 ≅ yR)
    (p1 : F.obj x ⟶ s1) (pR : F.obj xr ⟶ sr) (d : x ⟶ xr)
    (dS : sr ⟶ sR) (dY : y1 ⟶ yR) (dSupport : s1 ⟶ sr)
    (b1 : s1 ⟶ y1) (bR : sR ⟶ yR) (b0 : s0 ⟶ y0)
    (r : F.obj x0 ⟶ s0)
    (hn : F.map d ≫ pR = p1 ≫ dSupport)
    (ht : b1 ≫ dY = dSupport ≫ dS ≫ bR)
    (hs : F.map eX.hom ≫ pR ≫ dS = r ≫ eS.hom)
    (hy : bR ≫ eY.inv = eS.inv ≫ b0) :
    (p1 ≫ b1) ≫ (dY ≫ eY.inv) = F.map (d ≫ eX.inv) ≫ r ≫ b0 := by
  have hs' := congrArg (fun v ↦ F.map eX.inv ≫ v ≫ eS.inv) hs
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp, Iso.hom_inv_id, Category.comp_id] at hs'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht, ← reassoc_of% hn, hy, reassoc_of% hs']

private theorem reassociate_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {u v : D} {x y z : C} (a : u ⟶ v) (r : v ⟶ F.obj x)
    (p : x ⟶ y) (q : y ⟶ z) :
    a ≫ (r ≫ F.map p) ≫ F.map q = a ≫ r ≫ F.map (p ≫ q) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem transport_trace_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F0 : A ⥤ C) (F1 : B ⥤ D) (SX : A ⥤ B) (SY : C ⥤ D)
    (e : SX ⋙ F1 ≅ F0 ⋙ SY)
    {x0 X0 : A} {x1 X1 ar : B} {y0 Y0 r0 : C} {y1 Y1 r1 br : D}
    (ox0 : x0 ≅ X0) (ox1 : x1 ≅ X1) (oy0 : y0 ≅ Y0) (oy1 : y1 ≅ Y1)
    (a1 : x1 ⟶ ar) (a2 : ar ⟶ SX.obj x0)
    (b1 : y1 ⟶ br) (b2 : br ⟶ SY.obj y0)
    (p0 : F0.obj x0 ⟶ r0) (v0 : r0 ⟶ y0)
    (p1 : F1.obj x1 ⟶ r1) (v1 : r1 ⟶ y1)
    (h : (p1 ≫ v1) ≫ (b1 ≫ b2) =
      F1.map (a1 ≫ a2) ≫ e.hom.app x0 ≫ SY.map (p0 ≫ v0)) :
    (F1.map ox1.inv ≫ p1 ≫ v1 ≫ oy1.hom) ≫
        (oy1.inv ≫ b1 ≫ b2 ≫ SY.map oy0.hom) =
      F1.map (ox1.inv ≫ a1 ≫ a2 ≫ SX.map ox0.hom) ≫ e.hom.app X0 ≫
        SY.map (F0.map ox0.inv ≫ p0 ≫ v0 ≫ oy0.hom) := by
  have hn := e.hom.naturality ox0.hom
  dsimp only [Functor.comp_map] at hn
  have h' : p1 ≫ v1 ≫ b1 ≫ b2 =
      F1.map (a1 ≫ a2) ≫ e.hom.app x0 ≫ SY.map (p0 ≫ v0) := by
    simpa only [Category.assoc] using h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← SY.map_comp_assoc, ← F0.map_comp_assoc, Iso.hom_inv_id,
    F0.map_id, Category.id_comp]

private theorem outputTransition_eq
  (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
  (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
  coefCompactSupportNormalizedTau l E c K.obj n.le_succ =
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (normalizedDVRReductionTransition l E X D hl n.le_succ K.obj) ≫
      (finiteSupportRestriction l E c n.le_succ).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
  rw [← coefCompactSupportInputTau_eq D l hl E X K.obj n]
  unfold coefCompactSupportInputTau finiteSupportRestriction
    coefCompactSupportNormalizedTau coefCompactSupportTau
  exact map_insert_inv_hom _ _
    ((coefCompactSupportRestrictionIso l E X n.le_succ).app _) _ _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- Successor quotient compatibility of the specified finite relative trace.
Source: blueprint absolute structural trace and its coefficient counit squares
(blueprint: lem-coef-relative-trace-reduction).
Proof: use the structural counit squares and restriction/composition compatibility
on the etale site to obtain the etale relative trace square. Transport that square
through the intrinsic/site restriction square and the specified dualizing origins.
Naturality moves the origins past the restriction comparison and cancels their
inverse pairs, giving the displayed equality. -/
theorem finiteTrace_restriction (n : ℕ) :
  finiteTrace D l E f c (n + 1) ≫
      integralDualizingExceptionalTransition l E D Y hl n.le_succ =
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (integralDualizingExceptionalTransition l E D X hl n.le_succ) ≫
      (finiteSupportRestriction l E c n.le_succ).hom.app
        (integralDualizingFiniteTerm l E D X n) ≫
      (normalizedDVRRes l E Y n.le_succ).map (finiteTrace D l E f c n) := by
  let FX := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c
  let SY := normalizedDVRRes l E Y n.le_succ
  let VX := finiteDualizingRealization l E X (n + 1)
  let V := finiteDualizingRealization l E Y (n + 1)
  let V0 := finiteDualizingRealization l E Y n
  let K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))) :=
    ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩
  have hn := (finiteSupportRealization l E c (n + 1)).hom.naturality
    (ObjectProperty.homMk (X :=
      ⟨finiteDualizingEtaleTerm l E D X (n + 1),
        finiteEtaleDualizing_plus D l E X (n + 1)⟩)
      (Y := (Sheaf.restrictScalars X.smallEtaleTopology
      (finiteDualizingQuotient l E n.le_succ)).mapDerivedCategoryPlus.obj K)
      (finiteDualizingEtaleTransition l E D X n.le_succ))
  have ht := congrArg (fun v ↦ V.map v) (finiteEtaleTrace_restriction D l E f c n)
  have ht' : V.map (finiteEtaleTrace D l E f c (n + 1)) ≫
      V.map (finiteDualizingEtaleTransition l E D Y n.le_succ) =
    V.map ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c).map
        (finiteDualizingEtaleTransition l E D X n.le_succ)) ≫
      V.map (finiteEtaleSupportRestriction (finiteDualizingQuotient l E n.le_succ) c K) ≫
        V.map ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (finiteDualizingQuotient l E n.le_succ)).map (finiteEtaleTrace D l E f c n)) := by
    simpa only [V.map_comp] using ht
  have hs := finiteSupportRealization_restriction l E c n.le_succ K
  have hy := (finiteDualizingRealizationRestriction l E Y n.le_succ).inv.naturality
    (finiteEtaleTrace D l E f c n)
  have hreal := paste_trace_square FX
    ((finiteDualizingRealizationRestriction l E X n.le_succ).app K.obj)
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).obj K.obj))
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).app
      (finiteDualizingEtaleTerm l E D Y n))
    (finiteSupportOrigin D l E f c (n + 1)).hom
    ((finiteSupportRealization l E c (n + 1)).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology
        (finiteDualizingQuotient l E n.le_succ)).mapDerivedCategoryPlus.obj K))
    (VX.map (finiteDualizingEtaleTransition l E D X n.le_succ))
    (V.map (finiteEtaleSupportRestriction (finiteDualizingQuotient l E n.le_succ) c K))
    (V.map (finiteDualizingEtaleTransition l E D Y n.le_succ))
    (V.map ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c).map
        (finiteDualizingEtaleTransition l E D X n.le_succ)))
    (V.map (finiteEtaleTrace D l E f c (n + 1)))
    (V.map ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
      (finiteDualizingQuotient l E n.le_succ)).map (finiteEtaleTrace D l E f c n)))
    (SY.map (V0.map (finiteEtaleTrace D l E f c n)))
    ((finiteSupportRestriction l E c n.le_succ).hom.app
      ((finiteDualizingRealization l E X n).obj K.obj) ≫
      SY.map (finiteSupportOrigin D l E f c n).hom)
    hn ht' (hs.trans (Category.assoc _ _ _).symm) hy
  refine transport_trace_square
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c)
    FX (normalizedDVRRes l E X n.le_succ) SY (finiteSupportRestriction l E c n.le_succ)
    (finiteDualizingOrigin l E D X n) (finiteDualizingOrigin l E D X (n + 1))
    (finiteDualizingOrigin l E D Y n) (finiteDualizingOrigin l E D Y (n + 1))
    (VX.map (finiteDualizingEtaleTransition l E D X n.le_succ))
    ((finiteDualizingRealizationRestriction l E X n.le_succ).inv.app K.obj)
    (V.map (finiteDualizingEtaleTransition l E D Y n.le_succ))
    ((finiteDualizingRealizationRestriction l E Y n.le_succ).inv.app
      (finiteDualizingEtaleTerm l E D Y n))
    (finiteSupportOrigin D l E f c n).hom (V0.map (finiteEtaleTrace D l E f c n))
    (finiteSupportOrigin D l E f c (n + 1)).hom
    (V.map (finiteEtaleTrace D l E f c (n + 1))) ?_
  exact hreal.trans (reassociate_map SY _ _ _ _)

end WeilConjectures.CoefDualFormulaScalarTranspose

namespace WeilConjectures.CoefRelativeTrace

private theorem trace_coefficient_assembly
    {XA YA SA XB YB SB : Type*}
    [Category XA] [Category YA] [Category SA]
    [Category XB] [Category YB] [Category SB]
    (F : XA ⥤ YA) (G : YA ⥤ SA) (H : XA ⥤ SA)
    (F' : XB ⥤ YB) (G' : YB ⥤ SB) (H' : XB ⥤ SB)
    (TX : XA ⥤ XB) (TY : YA ⥤ YB) (TS : SA ⥤ SB)
    (a : F ⋙ G ⟶ H) (b : F' ⋙ G' ⟶ H')
    (cx : H ⋙ TS ⟶ TX ⋙ H') (cy : G ⋙ TS ⟶ TY ⋙ G')
    {R : SB ⥤ YB} (adj : G' ⊣ R)
    (W : XA) (V : YA) (W' : XB) (N : SA) (N' : SB)
    (ex : H.obj W ⟶ N) (ey : G.obj V ⟶ N)
    (ex' : H'.obj W' ⟶ N') (q : TS.obj N ⟶ N')
    (ux : (TX).obj W ⟶ W') (uy : (TY).obj V ⟶ R.obj N')
    (t : F.obj W ⟶ V) (t' : F'.obj W' ⟶ R.obj N')
    (cf : (TY).obj (F.obj W) ⟶ F'.obj ((TX).obj W))
    (ht : G.map t ≫ ey = a.app W ≫ ex)
    (ht' : G'.map t' ≫ adj.counit.app N' = b.app W' ≫ ex')
    (hx : cx.app W ≫ H'.map ux ≫ ex' = TS.map ex ≫ q)
    (hy : cy.app V ≫ G'.map uy ≫ adj.counit.app N' = TS.map ey ≫ q)
    (hc : cy.app (F.obj W) ≫ G'.map cf ≫ b.app ((TX).obj W) =
      TS.map (a.app W) ≫ cx.app W)
    [Epi (cy.app (F.obj W))] :
    (TY).map t ≫ uy = cf ≫ F'.map ux ≫ t' := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (cy.app (F.obj W))).1
  have hn := cy.naturality t
  dsimp only [Functor.comp_map] at hn
  have hb := b.naturality ux
  dsimp only [Functor.comp_map] at hb
  calc
    cy.app (F.obj W) ≫ G'.map ((TY).map t) ≫ G'.map uy ≫ adj.counit.app N' =
        TS.map (G.map t) ≫ TS.map ey ≫ q := by
          rw [← reassoc_of% hn, hy]
    _ = TS.map (a.app W) ≫ TS.map ex ≫ q := by
      rw [← TS.map_comp_assoc, ht, TS.map_comp]
      simp only [Category.assoc]
    _ = cy.app (F.obj W) ≫ G'.map cf ≫ G'.map (F'.map ux) ≫
        G'.map t' ≫ adj.counit.app N' := by
      rw [ht', reassoc_of% hb, reassoc_of% hc, hx]

end WeilConjectures.CoefRelativeTrace
