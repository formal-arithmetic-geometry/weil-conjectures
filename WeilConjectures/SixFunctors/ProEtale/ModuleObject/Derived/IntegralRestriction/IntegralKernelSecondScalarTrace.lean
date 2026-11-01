/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
import all WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPullbackCompatibility
import all WeilConjectures.AlgebraicGeometry.RationalP1.NormalizedScalarChernModel
import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Integral scalar trace compatibility for the second projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal SymmetricCategory.ofCurried
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 21000] CondensedRing.monoidal_upperStar
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory

attribute [local instance 20001] integral_trace_sheaf_symmetric

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction Mod.monoidalCategory Mod.monoidalClosed
set_option allowUnsafeReducibility true in
attribute [local reducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
  derivedUpper derivedLower derivedScalars internalScalarExtension Mod.regular
  internalMonoidal internalTensorBundle nativeTensorBundle
attribute [local irreducible] square
attribute [local irreducible] condensedAmbientPullbackComparison


attribute [local irreducible] derivedPullIso derivedPushHom

/-- The scalar exchange with the root-normalized integral line endpoint.
Source: the second projective-line triangle, scalar trace square.
(blueprint: lem-integral-kernel-second-scalar-trace). -/
@[irreducible]
def integralSecondTraceExchange (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)] :
    let Λ := Profinite.padicIntegersRingObj l E.val
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
        (traceTate l E (ProjectiveLine Y))) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (traceTate l E (diagonalSurface Y)) :=
  secondPretraceExchangeMap _ Y _ ≫
    (moduleObjectDerivedPushforward _ (secondProjection Y)).map
      (integralShiftedLinePullIso l E (firstProjection Y)).hom

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integral_exchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    derivedExchange Λ (ProjectiveLine Y ↘ Y) (secondProjection Y)
        (firstProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition.symm =
      condensedAmbientExchange Λ (square Y) := by
  have hc :
      (CondensedRing.leftDerivedUpperStarComp Λ (secondProjection Y)
          (ProjectiveLine Y ↘ Y)).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          (CondensedRing.upperStarCongr Λ
            (show secondProjection Y ≫ (ProjectiveLine Y ↘ Y) =
                firstProjection Y ≫ (ProjectiveLine Y ↘ Y) from pullback.condition.symm)) ≪≫
        CondensedRing.leftDerivedUpperStarComp Λ (firstProjection Y)
          (ProjectiveLine Y ↘ Y) =
        condensedAmbientPullbackComparison Λ (square Y) := by
    rw [derivedCongr_eq]
    unfold condensedAmbientPullbackComparison square
    rfl
  have hh := congrArg
    (fun t :
      moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (secondProjection Y) ⟶
        moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⋙
          moduleObjectDerivedPullback Λ (firstProjection Y) ↦
      (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
          (ProjectiveLine Y ↘ Y))
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y))
        (TwoSquare.mk _ _ _ _ t)).natTrans) (congrArg Iso.hom hc)
  unfold derivedExchange condensedAmbientExchange
  rw [Adjunction.exchangeRight_eq_mateEquiv]
  coefficient_finish hh

private def IntegralNativeTraceSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) : Prop :=
  (condensedAmbientExchange Λ (square Y)).app _ ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map e ≫
        (eqToIso d.p₂_canonical).inv.app _ ≫ d.trace₂ =
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      ((eqToIso d.q_canonical).inv.app _ ≫ d.traceq) ≫ (scalarUnitPullIso Λ Y).hom

set_option maxHeartbeats 800000 in
-- Paste normalized squares while keeping the coefficient category instances folded.
private theorem integralNativeTraceSquare_scalar
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X)
    (d : Diagram Λ Y L) (d' : Diagram Λ' Y L')
    (s : ScalarCompatibility a Y L L' m d d')
    {r : (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (firstProjection Y)).obj
      (L (ProjectiveLine Y)).X ⟶ (L (diagonalSurface Y)).X}
    {r' : (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (firstProjection Y)).obj
      (L' (ProjectiveLine Y)).X ⟶ (L' (diagonalSurface Y)).X}
    (e : PullEndpoint Λ (firstProjection Y) (L (ProjectiveLine Y))
      (L (diagonalSurface Y)) r)
    (e' : PullEndpoint Λ' (firstProjection Y) (L' (ProjectiveLine Y))
      (L' (diagonalSurface Y)) r')
    (hr : (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (firstProjection Y)).map (m
      (ProjectiveLine Y)) ≫ r' =
      r ≫ m (diagonalSurface Y))
    (h : IntegralNativeTraceSquare Λ Y L d (nativePullEndpointShift e)) :
    IntegralNativeTraceSquare Λ' Y L' d' (nativePullEndpointShift e') := by
  let V := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
  let b := (derivedPushHom a (ProjectiveLine Y ↘ Y)).app V ≫
    (moduleObjectDerivedPushforward Λ' (ProjectiveLine Y ↘ Y)).map (s.lineP.shift a)
  have hb : IsIso b := by
    have hp := normalized_push a (ProjectiveLine Y ↘ Y) d.Rq d'.Rq
      d.q_canonical d'.q_canonical d.q_unit d'.q_unit s.q.square V
    have : IsIso ((s.q.square.mate a).app V) := s.q.comparison_iso
    have : IsIso ((derivedPushHom a (ProjectiveLine Y ↘ Y)).app V) := by
      apply IsIso.of_isIso_fac_left hp
    dsimp only [b]
    unfold Endpoint.shift
    infer_instance
  have hq := nativeTrace_scalar a (ProjectiveLine Y ↘ Y)
    (s.units Y) s.lineP d.Rq d'.Rq d.q_canonical d'.q_canonical
    d.q_unit d'.q_unit d.traceq d'.traceq s.q
  have hp := nativeTrace_scalar a (secondProjection Y)
    (s.units (ProjectiveLine Y)) s.lineW d.R₂ d'.R₂ d.p₂_canonical d'.p₂_canonical
    d.p₂_unit d'.p₂_unit d.trace₂ d'.trace₂ s.p₂
  have hu := unit_pull_scalar a Y (s.units Y)
    (s.units (ProjectiveLine Y))
  have he := endpoint_pull_square_shift a (firstProjection Y) s.lineP s.lineW e e' hr
  have hx := coefficient_exchange_line
    (condensedAmbientExchange Λ (square Y))
    (condensedAmbientExchange Λ' (square Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y))
    (derivedPullIso a (firstProjection Y)).hom
    (derivedPushHom a (ProjectiveLine Y ↘ Y)) (derivedPushHom a (secondProjection Y))
    (s.lineP.shift a) (nativePullEndpointShift e) (nativePullEndpointShift e') (s.lineW.shift a)
    (flat_coefficient_exchange a (square Y) V) he
  have hh := trace_square_transport
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y))
    (derivedScalars a Y) (derivedScalars a (ProjectiveLine Y))
    (derivedPullIso a (ProjectiveLine Y ↘ Y))
    (s.units Y).iso.hom b (s.units (ProjectiveLine Y)).iso.hom
    ((derivedPushHom a (secondProjection Y)).app _ ≫
      (moduleObjectDerivedPushforward Λ' (secondProjection Y)).map (s.lineW.shift a))
    (scalarUnitPullIso Λ Y).hom (scalarUnitPullIso Λ' Y).hom
    _ _ _ _ _ _
    (by simpa only [b, Category.assoc] using hq)
    (by simpa only [Category.assoc] using hp) hu hx
    (by
      have h₀ := h
      dsimp only [IntegralNativeTraceSquare] at h₀
      simp only [Category.assoc] at h₀ ⊢
      coefficient_finish h₀)
  unfold IntegralNativeTraceSquare
  simp only [Category.assoc] at hh ⊢
  coefficient_finish hh

set_option maxHeartbeats 800000 in
-- Compose equalities of the two boundaries without dependent rewriting of the square.
private theorem integralNativeTraceSquare_of_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    {r : (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (firstProjection Y)).obj
      (L (ProjectiveLine Y)).X ⟶ (L (diagonalSurface Y)).X}
    (e : PullEndpoint Λ (firstProjection Y) (L (ProjectiveLine Y))
      (L (diagonalSurface Y)) r)
    (h : TracePullback Λ (ProjectiveLine Y ↘ Y) (secondProjection Y)
      (firstProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition.symm
      d.Rq d.R₂ d.q_canonical d.p₂_canonical e
      (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)) d.traceq d.trace₂) :
    IntegralNativeTraceSquare Λ Y L d (nativePullEndpointShift e) := by
  have hh := nativeTrace_pullback Λ (ProjectiveLine Y ↘ Y) (secondProjection Y)
    (firstProjection Y) (ProjectiveLine Y ↘ Y) pullback.condition.symm
    d.Rq d.R₂ d.q_canonical d.p₂_canonical e
    (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)) d.traceq d.trace₂ h
  have hu := unitPullEndpoint_eq Λ Y
    (nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y))
  unfold IntegralNativeTraceSquare
  rw [← integral_exchange_eq]
  have h' := hh.trans (congrArg
    (fun t ↦ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      ((eqToIso d.q_canonical).inv.app _ ≫ d.traceq) ≫ t) hu)
  coefficient_finish h'

attribute [local irreducible] condensedAmbientExchange

set_option maxHeartbeats 800000 in
-- Convert the native trace boundary with abstract coefficient and line objects.
private theorem integralNativeTraceSquare_to_second
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (h : IntegralNativeTraceSquare Λ Y L d e.hom) :
    secondPretraceExchangeMap Λ Y
        (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
          (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map e.hom ≫
      (secondDiagramPushIso Λ Y L d).inv.app
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ≫
      d.trace₂ ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      (RationalP1.trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫
        (secondTraceUnitIso Λ Y).hom := by
  have ht := congrArg (fun z ↦ z ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom) h
  unfold secondPretraceExchangeMap
  simp only [secondDiagramPushIso, RationalP1.trace, scalarUnitPullIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, id] at ht ⊢
  have ha := Category.assoc
    ((eqToIso d.p₂_canonical).inv.app
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
    d.trace₂ (singleUnitIso Λ (ProjectiveLine Y)).hom
  erw [ha] at ht
  coefficient_finish ht

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integralPullEndpoint_shift (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    nativePullEndpointShift (integralPullEndpoint l E f) =
      (integralShiftedLinePullIso l E f).hom := by
  have h := endpointShift_iso_formula (integralPullEndpoint l E f)
  unfold integralShiftedLinePullIso
  simpa only [id, integralPullEndpoint, cartesianPullEndpoint, integralLinePullIso] using h

set_option maxHeartbeats 3200000 in
-- The final scalar square converts several native derived presentations.
/-- The normalized integral trace commutes with the self-square exchange.
Source: the integral projective-line triangle calculation, trace base change.
(blueprint: lem-integral-kernel-second-scalar-trace).
Proof: the completed trace pullback theorem gives the Z_l square for q and p2
with the root-normalized first-projection endpoint. Transport the completed
reference to the Z_l family. Extend this square by the flat integral coefficient
map. The scalar exchange cube identifies its exchange with the canonical mate;
the two scalar trace squares identify its traces with those of Family.integral.
The scalar line square follows from naturality of integral root comparisons.
Cancel the invertible scalar source comparison. Finally identify the endpoint
with integralShiftedLinePullIso and conjugate the units to native tensor units. -/
theorem integralKernel_second_scalar_trace
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤))) :
    let Λ := Profinite.padicIntegersRingObj l E.val
    let L := fun X ↦ spIntegralTwist X l E
    let d := family.integral E
    integralSecondTraceExchange l E Y ≫
      (secondDiagramPushIso Λ Y L d).inv.app (traceTate l E (diagonalSurface Y)) ≫
      d.trace₂ ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫ (secondTraceUnitIso Λ Y).hom := by
  obtain ⟨line₀⟩ := zlPullEndpoint_nonempty l (firstProjection Y)
  let c₀ := nativeUnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l])
    (ProjectiveLine Y ↘ Y)
  have hz := tracePullback_of_realized l
    (ProjectiveLine Y ↘ Y) (secondProjection Y) (firstProjection Y)
    (ProjectiveLine Y ↘ Y)
    (by simpa only [firstProjection, secondProjection] using
      IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    hY hP reference.eP reference.eY reference.eW reference.eP reference.tq reference.t₂
    family.zl.Rq family.zl.R₂ family.zl.q_canonical family.zl.p₂_canonical
    family.zl.q_unit family.zl.p₂_unit reference.q_square reference.p₂_square line₀ c₀
    _ _ reference.q_trace reference.p₂_trace
  have hzl := integralNativeTraceSquare_of_pullback _ Y (zlLine l) family.zl line₀ hz
  have h : IntegralNativeTraceSquare (Profinite.padicIntegersRingObj.{u} l E.val) Y
      (fun X ↦ spIntegralTwist X l E) (family.integral E)
      (nativePullEndpointShift (integralPullEndpoint l E (firstProjection Y))) := by
    have : ∀ S : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (integralMap l E) S)) :=
      (integralScalarComparison_isIso l E (ProjectiveLine Y ↘ Y)).choose
    apply integralNativeTraceSquare_scalar (integralMap l E) Y _ _ _ _ _
      (family.toIntegral E) line₀ (integralPullEndpoint l E (firstProjection Y)) _ hzl
    exact (adicComparison l (firstProjection Y)).integral_inclusion
      (bottomField l) E (by
        change (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.val
        exact bot_le)
  rw [integralPullEndpoint_shift] at h
  unfold integralSecondTraceExchange
  simpa only [Category.assoc, traceTate] using
    integralNativeTraceSquare_to_second _ Y _ (family.integral E)
      (integralShiftedLinePullIso l E (firstProjection Y)) h


set_option maxHeartbeats 1600000 in
-- Extracting the completed reference and checking its derived models needs more elaboration time.
/-- Extract the scalar second-trace equality from the completed integral reference. -/
private theorem integral_reference_second_scalar_trace_cached
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (family : Family l Y) (href : IntegralFamilyReference l Y family) :
    let Λ := Profinite.padicIntegersRingObj l E.val
    let L := fun X ↦ spIntegralTwist X l E
    let d := family.integral E
    integralSecondTraceExchange l E Y ≫
      (secondDiagramPushIso Λ Y L d).inv.app (traceTate l E (diagonalSurface Y)) ≫
      d.trace₂ ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map
      (trace Λ Y L d ≫ (singleUnitIso Λ Y).hom) ≫ (secondTraceUnitIso Λ Y).hom := by
  let q := ProjectiveLine Y ↘ Y
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian (ProjectiveLine Y) := isNoetherian_of_locallyOfFiniteType q
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  obtain ⟨hY, aY, aP, aW, δ, ⟨reference⟩⟩ := href
  let := aY
  let := aP
  let := aW
  let : ∀ x : Y, Invertible (l : Y.residueField x) := fun x ↦
    (residueIsUnit l k (ringChar k) (Fact.out : ringChar k ≠ l) Y
      (Y ↘ Spec (.of k)) x).invertible
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map q.appTop.hom
  exact integralKernel_second_scalar_trace l E Y δ family reference hY hP

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
