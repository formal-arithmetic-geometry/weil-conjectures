/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondScalarTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondPullSection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondTraceEquation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondProjectionInterchange
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretrace
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondExchangeProjectionNative
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondTraceReordering

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Integral second trace reordering from the scalar trace square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate
attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] square condensedAmbientExchange

set_option maxHeartbeats 6400000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem integral_pretrace
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y))
    (hq : IsIso (projectionMap (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
        (ProjectiveLine Y))
        0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧)))
    (hx : IsIso (integralSecondTraceExchange l E Y)) :
    SecondPretraceEquation (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦ spIntegralTwist X l
      E)
      (integralShiftedLinePullIso l E (secondProjection Y))
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj K))
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj
          (K ⊗ (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val)
            (ProjectiveLine Y ↘ Y)).obj
              (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
                (ProjectiveLine Y)) 0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧))))
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (secondProjection
        Y)).obj
        (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
          (diagonalSurface Y))
          0).obj (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧))
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y
        ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
          (ProjectiveLine Y))
          0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧))
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).map
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).map
          (counitProjectionPart (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
            (ProjectiveLine Y) l E) K hq)))
      (@inv _ _ _ _ (integralSecondTraceExchange l E Y) hx)
      (secondTraceStrength (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
        (ProjectiveLine Y) l E) K
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine
          Y ↘ Y)).obj
          (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
            (ProjectiveLine Y))
            0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧))).hom
      (integralSecondForwardProjection l E Y K) := by
  let Λ := (Profinite.padicIntegersRingObj l E.val)
  let F : DerivedCategory (Modules Λ Y) ⥤
      DerivedCategory (Modules Λ (ProjectiveLine Y)) :=
    moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let R : DerivedCategory (Modules Λ (ProjectiveLine Y)) ⥤
      DerivedCategory (Modules Λ Y) :=
    moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
  let H := twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧
  let M := (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
    (spIntegralTwist (ProjectiveLine Y) l E)).obj
      ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
        Y)).obj K)
  let a := projectionMap Λ (ProjectiveLine Y ↘ Y) K T
  let t := tensorShiftIso Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E) (F.obj K)
  let b := secondPretraceExchangeMap Λ Y M
  let β := integralSecondTraceExchange l E Y
  let s := secondTraceStrength Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K (R.obj T)
  have haIso : IsIso a := hq
  have hxIso : IsIso β := hx
  have htwo := integralKernel_second_projection_interchange l E Y K (R.obj T) β
  have he := native_twisted_self_square Λ Y
    (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
    (integralShiftedLinePullIso l E (firstProjection Y)) K
  dsimp only at he
  rw [← pretrace_native] at he
  change F.map a ≫ F.map (R.map t.hom) ≫ b = _ at he
  have he' : F.map a ≫ F.map (R.map t.hom) ≫ b =
      (secondTraceTensorIso Λ Y K (R.obj T)).inv ≫ (F.obj K ◁ β) ≫
        nativeSecondExtractProjection Λ Y (spIntegralTwist (ProjectiveLine Y) l E)
          (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (firstProjection Y)) K := by
    simpa only [β, integralSecondTraceExchange] using he
  let τ := twistProjectionMap Λ (secondProjection Y)
    (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
    (integralShiftedLinePullIso l E (secondProjection Y))
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)
  have h : s.hom ≫ H.map (F.map a ≫ (F.mapIso (R.mapIso t)).hom ≫ b) ≫ τ =
      (M ◁ β) ≫ integralSecondForwardProjection l E Y K :=
    transport_forward H s.hom τ (M ◁ β)
      (integralSecondForwardProjection l E Y K) he' htwo
  have hc : counitProjectionPart Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K hq =
      R.map t.inv ≫ inv a := by
    unfold counitProjectionPart
    rfl
  exact generic_record_assembly Λ Y (fun X ↦ spIntegralTwist X l E) (integralShiftedLinePullIso l
    E (secondProjection Y))
    (K ⊗ R.obj T) (F.obj K ⊗ T) M (R.obj T)
    ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧))
    a haIso t (counitProjectionPart Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K hq)
    β hxIso s.hom (integralSecondForwardProjection l E Y K) hc h

set_option maxHeartbeats 6400000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
/-- Scalar trace compatibility gives the full integral trace-tail equation.
Source: the integral projective-line triangle calculation, second identity.
(blueprint: lem-integral-kernel-second-trace-reordering).
Proof: the native exchange/projection square, followed by integral two-factor
projection interchange, gives the forward square. Invert it using the specified
projection and exchange isomorphisms; generic_record_assembly records this as the
pretrace equation. Factor the counit into inverse projection and scalar trace.
Monoidal strength evaluation moves this trace to its scalar factor. The given
scalar trace square cancels the inverse scalar exchange and leaves exactly trace2.
All other factors are canonical tensor and right-unitor comparisons. -/
theorem integralKernel_second_trace_reordering
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (family : Family l Y)
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y))
    (ε : (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine
      Y ↘ Y)).obj
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj K)) ⟶ K)
    (_hε : CounitComponentNormalized (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦
      spIntegralTwist X l E)
      (family.integral E) K ε)
    (hx : IsIso (integralSecondTraceExchange l E Y))
    (ht : integralSecondTraceExchange l E Y ≫
      (secondDiagramPushIso (Profinite.padicIntegersRingObj l E.val) Y
        (fun X ↦ spIntegralTwist X l E) (family.integral E)).inv.app
          (traceTate l E (diagonalSurface Y)) ≫
      (family.integral E).trace₂ ≫
      (singleUnitIso (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
        (ProjectiveLine Y ↘ Y)).map
          (trace (Profinite.padicIntegersRingObj l E.val) Y
            (fun X ↦ spIntegralTwist X l E) (family.integral E) ≫
              (singleUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom) ≫
        (secondTraceUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom) :
    SecondTraceEquation (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦ spIntegralTwist X l E)
      (family.integral E)
      (integralShiftedLinePullIso l E (secondProjection Y))
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj K))
      ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).map
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).map ε))
      (integralSecondForwardProjection l E Y K) := by
  obtain ⟨hq, hε⟩ := _hε
  have he : ε = counitComponent (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦
    spIntegralTwist X l E)
      (family.integral E) K hq := eq_of_heq hε
  subst ε
  let := hx
  constructor
  intro hb hp
  have hpre := (integral_pretrace l E Y K hq hx).equation hb hp
  have heval := secondTraceStrength_evaluation (Profinite.padicIntegersRingObj l E.val) Y
    (spIntegralTwist (ProjectiveLine Y) l E) K
    ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
      Y)).obj
      (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
        (ProjectiveLine Y))
        0).obj (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧))
    (trace (Profinite.padicIntegersRingObj l E.val) Y (fun X ↦ spIntegralTwist X l E)
      (family.integral E) ≫
      (singleUnitIso (Profinite.padicIntegersRingObj l E.val) Y).hom)
  have hscalar := congrArg (fun a ↦ inv (integralSecondTraceExchange l E Y) ≫ a) ht
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id_assoc] at hscalar
  rw [counitComponent_factor]
  simp only [Functor.map_comp, Category.assoc] at heval ⊢
  rw [reassoc_of% hpre, heval]
  simp only [← whiskerLeft_comp_assoc]
  rw [hscalar]


end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
