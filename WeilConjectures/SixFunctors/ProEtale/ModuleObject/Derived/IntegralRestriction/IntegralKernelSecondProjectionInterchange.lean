/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondPullSection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSecondExtractProjection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondTateSymmetry
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionTailCore
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeCore

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Integral two-factor projection interchange -/

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
attribute [local irreducible] twist projectionMap tensorShiftIso twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] square condensedAmbientExchange

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem strength_naturality
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K V : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y))
    (Q R Z : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)))
    (z : (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
      Y)).obj V ⟶ Q)
    (q : ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y
      ↘ Y)).obj K) ⊗ Q ⟶ R)
    (τ : (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
      (ProjectiveLine Y) l E)).obj R ⟶ Z) :
    (secondTraceStrength (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
      (ProjectiveLine Y) l E) K V).hom ≫
        (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
          (ProjectiveLine Y) l E)).map
          ((secondTraceTensorIso (Profinite.padicIntegersRingObj l E.val) Y K V).inv ≫
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
              (ProjectiveLine Y ↘ Y)).obj K ◁ z) ≫ q) ≫ τ =
      (((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
        (ProjectiveLine Y) l E)).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
          Y)).obj K)) ◁ z) ≫
        secondTraceStrengthTail (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
          (ProjectiveLine Y) l E) K Q ≫
        (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
          (ProjectiveLine Y) l E)).map q ≫ τ := by
  let Λ := (Profinite.padicIntegersRingObj l E.val)
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let H := twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
    (spIntegralTwist (ProjectiveLine Y) l E)) ⟦(2 : ℤ)⟧
  let := secondTracePullMonoidal Λ Y
  let := secondTraceBraided Λ Y
  have hstrength :
      (secondTraceStrength Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K V).hom ≫
          H.map ((secondTraceTensorIso Λ Y K V).inv ≫ (F.obj K ◁ z)) =
        (H.obj (F.obj K) ◁ z) ≫
          secondTraceStrengthTail Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K Q := by
    rw [Functor.map_comp]
    simp only [secondTraceStrength, secondTraceStrengthTail, secondTraceTensorIso,
      secondTraceSwap, Iso.trans_hom, Iso.symm_hom, tensorIso, Iso.refl_hom,
      Functor.Monoidal.μIso]
    dsimp only [H, F]
    simp only [Category.assoc]
    rw [← reassoc_of% (tensorShiftIso_naturality Λ (ProjectiveLine Y)
      (spIntegralTwist (ProjectiveLine Y) l E)
      (Functor.OplaxMonoidal.δ
        (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) K V))]
    rw [← tensorShiftIso_naturality (Profinite.padicIntegersRingObj l E.val)
      (ProjectiveLine Y)
      (spIntegralTwist (ProjectiveLine Y) l E)
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K ◁ z)]
    simp only [tensorHom_id]
    simpa only [secondTraceTensorIso, Functor.Monoidal.μIso, tensorIso,
      Iso.refl_hom, tensorHom_id, id_tensorHom] using
      conjugatedTail_naturality
      (tensorShiftIso Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))
      (tensorShiftIso Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
        (((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q))
      (secondTraceTensorIso Λ Y K V) z
  have hstrength' :
      (secondTraceStrength (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
        (ProjectiveLine Y) l E) K V).hom ≫
          (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
            (spIntegralTwist (ProjectiveLine Y) l E)).map
            ((secondTraceTensorIso (Profinite.padicIntegersRingObj l E.val) Y K V).inv ≫
              ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
                (ProjectiveLine Y ↘ Y)).obj K ◁ z)) =
        (((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) l E)).obj
          ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
            (ProjectiveLine Y ↘ Y)).obj K)) ◁ z) ≫
          secondTraceStrengthTail (Profinite.padicIntegersRingObj l E.val) Y
            (spIntegralTwist (ProjectiveLine Y) l E) K Q := by
    simpa only [Λ, F, H] using hstrength
  calc
    (secondTraceStrength (Profinite.padicIntegersRingObj l E.val) Y (spIntegralTwist
      (ProjectiveLine Y) l E) K V).hom ≫
          (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
            (spIntegralTwist (ProjectiveLine Y) l E)).map
            ((secondTraceTensorIso (Profinite.padicIntegersRingObj l E.val) Y K V).inv ≫
              ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
                (ProjectiveLine Y ↘ Y)).obj K ◁ z) ≫ q) ≫ τ =
        ((secondTraceStrength (Profinite.padicIntegersRingObj l E.val) Y
          (spIntegralTwist (ProjectiveLine Y) l E) K V).hom ≫
          (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
            (spIntegralTwist (ProjectiveLine Y) l E)).map
            ((secondTraceTensorIso (Profinite.padicIntegersRingObj l E.val) Y K V).inv ≫
              ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val)
                (ProjectiveLine Y ↘ Y)).obj K ◁ z))) ≫
          (twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y)
            (spIntegralTwist (ProjectiveLine Y) l E)).map q ≫ τ := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hstrength']; simp only [Category.assoc]

set_option maxHeartbeats 3200000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem projection_tail
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y)) :
    let Λ := (Profinite.padicIntegersRingObj l E.val)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
    let Q := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧)
    let T := (((DerivedCategory.singleFunctor
      (Modules Λ (diagonalSurface Y)) 0).obj (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧)
    secondTraceStrengthTail Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K Q ≫
        H.map (nativeSecondExtractProjection (Profinite.padicIntegersRingObj l E.val) Y
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (firstProjection Y)) K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (secondProjection Y))
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      (projectionMap Λ (secondProjection Y))
        (H.obj (F.obj K)) T ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (tensorHom (integralSecondPullComparison l E Y K).inv (𝟙 T) ≫
            (tensorShiftIso Λ (diagonalSurface Y) (spIntegralTwist (diagonalSurface Y) l E)
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
            (H.obj (F.obj K)))).hom) := by
  let Λ := (Profinite.padicIntegersRingObj l E.val)
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let P := moduleObjectDerivedPullback Λ (secondProjection Y)
  let P₁ := moduleObjectDerivedPullback Λ (firstProjection Y)
  let R := moduleObjectDerivedPushforward Λ (secondProjection Y)
  let LS := spIntegralTwist (ProjectiveLine Y) l E
  let LX := spIntegralTwist (diagonalSurface Y) l E
  let H := twist Λ (ProjectiveLine Y) LS
  let J := twist Λ (diagonalSurface Y) LX
  let T := (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LX)
    ⟦(2 : ℤ)⟧)
  let D := P₁.obj (H.obj A)
  let e₁ := integralShiftedLinePullIso l E (firstProjection Y)
  let e₂ := integralShiftedLinePullIso l E (secondProjection Y)
  let a := pullTwistIso Λ (firstProjection Y) LS LX e₁ A
  let d := pullTwistIso Λ (secondProjection Y) LS LX e₂ A
  let b := (ambientPullbackComparison Λ (square Y)).app K
  let x := extractionInsideMap Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b
  have hc : d.hom ≫ J.map b.hom ≫ a.inv =
      (integralSecondPullComparison l E Y K).inv := by
    unfold integralSecondPullComparison
    exact inverse_comparison J (ambientPullbackComparison Λ (square Y)) K a d
  have hb : (tensorBraiding Λ (diagonalSurface Y) T T).hom = 𝟙 (T ⊗ T) :=
    integralKernel_second_tate_symmetry l E (diagonalSurface Y)
  have hi := comparison_tail J T
    (tensorShiftIso Λ (diagonalSurface Y) LX (P.obj A))
    (tensorShiftIso Λ (diagonalSurface Y) LX (P₁.obj A))
    (tensorShiftIso Λ (diagonalSurface Y) LX (P.obj A ⊗ T))
    (tensorShiftIso Λ (diagonalSurface Y) LX D) a d b
    (tensorBraiding Λ (diagonalSurface Y) T T).hom hb x
    (extractionInsideMap_eq Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b)
    (tensorShiftIso_naturality Λ (diagonalSurface Y) LX x).symm
    (tensorShiftIso_naturality Λ (diagonalSurface Y) LX
      (A := P.obj A) (B := P₁.obj A) b.hom)
  have he := congrArg
    (fun f : P.obj (H.obj A) ⟶ D ↦
      (f ▷ T) ≫ (tensorShiftIso Λ (diagonalSurface Y) LX D).hom) hc
  have hi := hi.trans he
  have hp := second_trace_strength_projection_action Λ Y (diagonalSurface Y)
    (secondProjection Y) LS LX e₂ K T D x
  have hir := congrArg
    (fun f : P.obj (H.obj A) ⊗ T ⟶ J.obj D ↦
      projectionMap Λ (secondProjection Y) (H.obj A) T ≫ R.map f) hi
  have hp := hp.trans hir
  have hex : nativeSecondExtractProjection (Profinite.padicIntegersRingObj l E.val) Y
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (firstProjection Y)) K =
      projectionMap Λ (secondProjection Y) A T ≫ R.map x := by
    exact (native_extract_generic Λ Y LS LX e₁ K).trans
      (extractionProjectionMap_eq Λ (secondProjection Y) (firstProjection Y) LS LX e₁ A b)
  have hl := congrArg
    (fun f : A ⊗ R.obj T ⟶ R.obj D ↦
      secondTraceStrengthTail Λ Y LS K (R.obj T) ≫ H.map f ≫
        twistProjectionMap Λ (secondProjection Y) LS LX e₂ D) hex
  have hr := congrArg
    (fun f : P.obj (H.obj A) ⊗ T ⟶ D ⊗ T ↦
      projectionMap Λ (secondProjection Y) (H.obj A) T ≫ R.map
        (f ≫ (tensorShiftIso Λ (diagonalSurface Y) LX D).hom))
    (tensorHom_id (integralSecondPullComparison l E Y K).inv T)
  exact hl.trans (hp.trans hr.symm)

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
/-- Move an outside even integral Tate line across the forward projection.
Source: the integral projective-line triangle calculation, second identity.
(blueprint: lem-integral-kernel-second-projection-interchange).
Proof: expand the monoidal strength and cancel its tensorator against its inverse.
Naturality of the tensor-shift comparison moves the arbitrary scalar arrow to the
front. The two-factor projection identity expresses the remaining tail by its
inside tensor maps. The integral shifted Tate line has identity self-braiding,
so its two transpositions cancel. Tensor-shift naturality and the self-square
pullback comparison leave precisely the inverse integral pull comparison. -/
theorem integralKernel_second_projection_interchange
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K V : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) Y))
    (z : (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
      Y)).obj V ⟶
      (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.val) (secondProjection
        Y)).obj
        (((DerivedCategory.singleFunctor (Modules (Profinite.padicIntegersRingObj l E.val)
          (diagonalSurface Y))
          0).obj (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧)) :
    let Λ := (Profinite.padicIntegersRingObj l E.val)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)
    (secondTraceStrength Λ Y (spIntegralTwist (ProjectiveLine Y) l E) K V).hom ≫
        H.map ((secondTraceTensorIso Λ Y K V).inv ≫
          (F.obj K ◁ z) ≫ nativeSecondExtractProjection (Profinite.padicIntegersRingObj l E.val) Y
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (firstProjection Y)) K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (secondProjection Y))
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      (H.obj (F.obj K) ◁ z) ≫ integralSecondForwardProjection l E Y K := by
  dsimp
  let Λ := (Profinite.padicIntegersRingObj l E.val)
  have h := (strength_naturality l E Y K V
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (spIntegralTwist (diagonalSurface Y) l E)) ⟦(2 : ℤ)⟧))
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
          ((twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)).obj
            ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))))
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (spIntegralTwist (diagonalSurface Y) l E)).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
            ((twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)).obj
              ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))))) z
      (nativeSecondExtractProjection (Profinite.padicIntegersRingObj l E.val) Y
          (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
          (integralShiftedLinePullIso l E (firstProjection Y)) K)
      (twistProjectionMap Λ (secondProjection Y)
        (spIntegralTwist (ProjectiveLine Y) l E) (spIntegralTwist (diagonalSurface Y) l E)
        (integralShiftedLinePullIso l E (secondProjection Y))
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
          ((twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) l E)).obj
            ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)))
  ))
  rw [h]
  unfold integralSecondForwardProjection
  exact congrArg (fun f ↦
    ((twist (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y) (spIntegralTwist
      (ProjectiveLine Y) l E)).obj
      ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj l E.val) (ProjectiveLine Y ↘
        Y)).obj K) ◁ z) ≫ f)
    (projection_tail l E Y K)

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
