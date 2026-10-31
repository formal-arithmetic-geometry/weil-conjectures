/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingProjection

/-! # The integral left projection on localizing objects -/
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
open DiagonalCoefficients CondensedRing

/-- The native left projection is invertible over O_E on Loc(Dbc).
Source: integral restriction proof, paragraph (1), using the integral proper
projection formula (blueprint: lem-integral-kernel-projection).
Proof: apply the integral proper projection theorem to the two localizing objects.
Its right-coefficient projection is the published derived adjunction mate.
Conjugating with the native Koszul braidings gives traceProjection, and the
normalized projection family's defining equality gives the stated map. -/
theorem integral_kernel_projection_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f]
    (M : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) S))
    (N : DerivedCategory (Modules (Profinite.padicIntegersRingObj l E.val) X))
    (hM : localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj l E.val) S) M)
    (hN : localizingClosure
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj l E.val) X) N) :
    IsIso (projectionMap (Profinite.padicIntegersRingObj l E.val) f M N) := by
  let Λ := Profinite.padicIntegersRingObj l E.val
  have h := (integralProperProjectionFormula l E k f).2.2 N M hN hM
  have hm : IsIso (moduleObjectProjectionMate Λ f N M) := by
    rw [normalizedMate_eq_published]
    exact (canonical_projection_isIso Λ f N M).mp h
  unfold projectionMap
  exact normalized_projection_isIso Λ (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec f M N hm
end AlgebraicGeometry.ProEtale.RationalP1
