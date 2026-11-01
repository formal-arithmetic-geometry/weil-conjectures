/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelFirstAmbientFormula
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelFirstTransport
public import WeilConjectures.AlgebraicGeometry.RationalP1.SectionEvaluationCongruence
/-! # Split integral diagonal contraction -/
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
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
/-- This is the first (pushforward) contraction, a strict component of
`integralKernel_contractions`.
Source: sk-thm-int-restriction-line.proof.md, paragraph (1).
(blueprint: lem-integral-kernel-first-contraction).
The proof transports the corresponding trace/base-change rearrangement and section
normalization through the canonical integral coefficient reference. -/
theorem integralKernel_first_contraction
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
    (hr : ∀ K, IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveSpace (ULift.{u} (Fin 2)) Y) K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val)
          (ProjectiveSpace (ULift.{u} (Fin 2)) Y ↘ Y)).obj K))
    (family : Family ℓ Y) (_href : IntegralFamilyReference ℓ Y family)
    (a : IntegralUnitCounitType ℓ E Y hq hr)
    (_hnorm : IntegralUnitCounitNormalized ℓ E Y hq hr family a) :
       (∀ M,
      (((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).map (a.1.app M)) ≫
        a.2.app ((restrictedPush ℓ E (ProjectiveLine Y ↘ Y) hr).obj M)).hom =
      (moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        (ProjectiveLine Y ↘ Y)).map
        ((ρ_ M.obj).inv ≫ (M.obj ◁
          ((RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y)).inv ≫ (family.integral E).support₁.hom ≫
            (family.integral E).R₁.R.map (family.integral E).delta ≫
            (family.integral E).trace₁ ≫
            (RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y)).hom)) ≫ (ρ_ M.obj).hom)) := by
  intro M
  obtain ⟨u, v, hu, hv, htransport⟩ := integralKernel_first_transport
    ℓ E k Y hq hr family _href a _hnorm M
  have hambient := integralKernel_first_ambient_formula
    ℓ E k Y family _href M.obj M.property u v
      (by
        set_option backward.isDefEq.respectTransparency true in
          set_option backward.isDefEq.respectTransparency.types true in
            run_tac withMainContext do
              let goal ← getMainGoal
              let target ← goal.getType
              let val := (← getLocalDeclFromUserName `hu).toExpr
              Term.synthesizeSyntheticMVarsNoPostponing
              let val ← instantiateMVars val
              let actual ← inferType val
              unless actual.isAppOf ``RationalP1.UnitComponentNormalized &&
                  target.isAppOf ``RationalP1.UnitComponentNormalized do
                throwError "expected a normalized unit component"
              let xs := actual.getAppArgs
              let ys := target.getAppArgs
              let endpoint := xs[xs.size - 4]!
              let endpoint' := ys[ys.size - 4]!
              unless endpoint.isAppOfArity ``Eq.mp 4 do
                throwError "expected the canonical endpoint cast, got {endpoint}"
              let es := endpoint.getAppArgs
              let hcast ← mkAppM ``cast_heq #[es[2]!, es[3]!]
              let (hraw, _) ← (RationalP1.coefficientHEq es[3]! endpoint').run {}
              let he ← mkAppM ``HEq.trans #[hcast, hraw]
              let (h, _) ← (RationalP1.coefficientHEq actual target).run
                { proofs := #[(endpoint, endpoint', he)] }
              let result ← mkAppM ``Eq.mp #[← mkEqOfHEq h, val]
              goal.assign result
              replaceMainGoal [])
      (by
        set_option backward.isDefEq.respectTransparency true in
          set_option backward.isDefEq.respectTransparency.types true in
            section_evaluation_exact hv)
  exact htransport.trans hambient

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
