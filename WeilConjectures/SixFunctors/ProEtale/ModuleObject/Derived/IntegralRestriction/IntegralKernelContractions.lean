/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelFirstContraction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondContraction
/-! # The two integral diagonal contractions before integration
-/
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
/-- Before integration, the two normalized unit-counit composites are tensor
contractions with the two diagonal integrals. No adjunction is assumed. -/
theorem integralKernel_contractions
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
              (ProjectiveLine Y)).hom)) ≫ (ρ_ M.obj).hom)) ∧
    (∀ K,
      (a.1.app ((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K) ≫
        (restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).map (a.2.app K)).hom =
      (ρ_ (((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj)).inv ≫
        ((((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj) ◁
          ((RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y)).inv ≫ (family.integral E).support₂.hom ≫
            (family.integral E).R₂.R.map (family.integral E).delta ≫
            (family.integral E).trace₂ ≫
            (RationalP1.singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y)).hom)) ≫
        (ρ_ (((restrictedPull ℓ E (ProjectiveLine Y ↘ Y) 1 hq).obj K).obj)).hom) := by
  exact ⟨integralKernel_first_contraction ℓ E k Y hq hr family _href a _hnorm,
    integralKernel_second_contraction ℓ E k Y hq hr family _href a _hnorm⟩
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
