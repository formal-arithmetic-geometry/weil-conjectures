/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstSectionKernelComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import all WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace

/-! # Base change of the integral scalar trace -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing CondensedRing.IntegralRestriction
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 21000] CondensedRing.monoidal_upperStar
attribute [local instance 20000] ProEtale.sheafBraidedCategory ProEtale.sheafMonoidalCategory
attribute [local instance 20001] trace_sheaf_symmetric
attribute [local instance] trace_pull_shift trace_push_shift trace_scalar_shift
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction Mod.monoidalCategory Mod.monoidalClosed
attribute [local semireducible] traceTate
set_option maxHeartbeats 800000 in
-- Keep enough heartbeats for the fixed native derived comparison instances.
/-- The completed reference transports the first scalar trace square to integral
coefficients. Source: first identity of the projective-line triangle proof and
paragraph (1) of the integral restriction proof.
(blueprint: lem-integral-kernel-scalar-trace).
Proof: pull back the completed trace, identify its Z_l realization through the
full-unit-normalized reference squares, and extend scalars along Z_l to O_E.
The family's scalar compatibility square preserves the trace. The root comparison
is the specified integral line pullback; its single-degree and shift comparisons
are exactly integralShiftedLinePullIso. Convert the coefficient units to tensor units. -/
theorem integral_kernel_scalar_trace
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
    firstTraceExchange (Profinite.padicIntegersRingObj l E.val) Y
        (((DerivedCategory.singleFunctor (Modules
          (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)) 0).obj
            (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧)
        (((DerivedCategory.singleFunctor (Modules
          (Profinite.padicIntegersRingObj l E.val) (diagonalSurface Y)) 0).obj
            (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧)
        (by simpa only [traceTate] using
          (integralShiftedLinePullIso l E (secondProjection Y))) ≫
      firstNativeFunctional (Profinite.padicIntegersRingObj l E.val) Y
        (fun X ↦ spIntegralTwist X l E) (family.integral E)
        (((DerivedCategory.singleFunctor (Modules
          (Profinite.padicIntegersRingObj l E.val) (diagonalSurface Y)) 0).obj
            (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧) (family.integral E).trace₁ ≫
      (singleUnitIso (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
      (ProjectiveLine Y ↘ Y)).map
        (trace (Profinite.padicIntegersRingObj l E.val) Y
          (fun X ↦ spIntegralTwist X l E) (family.integral E) ≫
            (singleUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom) ≫
      (secondTraceUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom := by
  obtain ⟨line₀⟩ := zlPullEndpoint_nonempty l (secondProjection Y)
  let c₀ : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (ProjectiveLine Y ↘ Y) :=
    nativeUnitPullEndpoint _ _
  have hz := tracePullback_of_realized l
    (ProjectiveLine Y ↘ Y) (firstProjection Y) (secondProjection Y)
    (ProjectiveLine Y ↘ Y)
    (by simpa only [firstProjection, secondProjection] using
      (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).flip)
    hY hP reference.eP reference.eY reference.eW reference.eP reference.tq reference.t₁
    family.zl.Rq family.zl.R₁ family.zl.q_canonical family.zl.p₁_canonical
    family.zl.q_unit family.zl.p₁_unit reference.q_square reference.p₁_square line₀ c₀
    _ _ reference.q_trace reference.p₁_trace
  have hzl := nativeTraceSquare_of_pullback _ Y (zlLine l) family.zl line₀ hz
  have hi :
      NativeTraceSquare (Profinite.padicIntegersRingObj.{u} l E.1) Y
        (fun X ↦ spIntegralTwist X l E) (family.integral E)
        (nativePullEndpointShift (integralPullEndpoint l E (secondProjection Y))) := by
    have : ∀ S : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (integralMap l E) S)) :=
      (integralScalarComparison_isIso l E (ProjectiveLine Y ↘ Y)).choose
    apply nativeTraceSquare_scalar (integralMap l E) Y _ _ _ _ _
      (family.toIntegral E) line₀ (integralPullEndpoint l E (secondProjection Y)) _ hzl
    exact (adicComparison l (secondProjection Y)).integral_inclusion
      (bottomField l) E (by
        change (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≤ E.1
        exact bot_le)
  let e : (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
      (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
          (ProjectiveLine Y)) 0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
          (diagonalSurface Y)) 0).obj (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧ := by
    simpa only [traceTate] using integralShiftedLinePullIso l E (secondProjection Y)
  have he : nativePullEndpointShift (integralPullEndpoint l E (secondProjection Y)) =
      e.hom := by
    have hs := endpointShift_iso_formula (integralPullEndpoint l E (secondProjection Y))
    exact hs
  have hi' : NativeTraceSquare (Profinite.padicIntegersRingObj l E.val) Y
      (fun X ↦ spIntegralTwist X l E) (family.integral E) e.hom := by
    rw [← he]
    exact hi
  exact nativeTraceSquare_to_first (Profinite.padicIntegersRingObj l E.val) Y
    (fun X ↦ spIntegralTwist X l E) (family.integral E) e hi'
end AlgebraicGeometry.ProEtale.RationalP1
