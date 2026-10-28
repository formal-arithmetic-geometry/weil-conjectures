/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group C1
-/
module
public import Sheaf.SixFunctors.IntegralKernelUnitCounit
public import Sheaf.SixFunctors.IntegralNormalizedFamily
/-! # Transport from restricted to ambient first contraction -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
open RationalP1
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
/--
The normalized restricted components factor through ambient normalized components.
For each restricted object, the unit followed by the canonical ambient comparison and
the counit comparison give ambient maps `u` and `v`; their ambient composite is
exactly the original restricted composite after applying the pushforward.  This is
the formal transport part of the first contraction and is strictly smaller than the
geometric ambient trace/base-change calculation.
Source: `sk-thm-int-restriction-line.proof.md`, paragraph (1), normalization transport.
(blueprint: lem-integral-kernel-first-transport).
-/
theorem integralKernel_first_transport
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (hq : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y)
        ((pullTwistShift ℓ E (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y) 1).obj K))
    (hr : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) (_href : IntegralFamilyReference ℓ Y family)
    (a : IntegralUnitCounitType ℓ E Y hq hr)
    (_hnorm : IntegralUnitCounitNormalized ℓ E Y hq hr family a) :
    ∀ M, ∃ (u : M.obj ⟶
        (RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
          ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj)))
      (v : (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
        ((RationalP1.twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y ↘ Y)).obj
              ((moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj))) ⟶
        (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj),
      RationalP1.UnitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        (by simpa only [traceTate] using
          (integralShiftedLinePullIso ℓ E (RationalP1.secondProjection Y))) M.obj u ∧
      RationalP1.CounitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M.obj) v ∧
      (((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).map (a.1.app M)) ≫
        a.2.app ((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).obj M)).hom =
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map u ≫ v := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
