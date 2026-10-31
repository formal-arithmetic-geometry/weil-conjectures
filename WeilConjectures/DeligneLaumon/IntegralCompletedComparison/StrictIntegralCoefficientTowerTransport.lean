/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackRoosFiniteTower
import WeilConjectures.ProperBaseChange.IntegralStrictModelMatchingExists
import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.IntegralPullbackSignedShift
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransportProjections
import WeilConjectures.DeligneLaumon.IntegralCompletedComparison.StrictIntegralRoosTransportShifts

/-! # Coefficient transport before the completeness restriction

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-strict-integral-coefficient-tower-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

-- The existential projection property retains the named goodness hypothesis,
-- although its displayed equality does not depend on the proof of goodness.
set_option linter.unusedVariables false in
/-- Transport the published strict completed tower before restricting its domain.
The supplied finite maps fix the ordinary generators; the supplied reflector
comparison is fixed by its unit. No completeness predicate enters this result.

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5);
sites-cohomology.tex, Tag 0941; derived.tex, Tags 011G and 014E.
(blueprint: lem-a1-strict-integral-coefficient-tower-transport).

Proof: obtain the signed integral shift and its descent from the normalized finite
strict tower C. Apply the existing integral Roos finite-tower realization with
these shifts, obtaining r and its computation-projection and shift equations.
Choose a normalized ordinary pullback identification i and a strict Roos model
comparison q satisfying the existing model-matching predicate. Recode q through
the two exact coefficient equivalences to get the constructed isomorphism j from
the published strict pullback to the integral Roos pullback. Set b = j followed
by r. Reassociate its nth computation projection, substitute the projection
formula for r, and apply the normalized projection compatibility for j.
The unit-normalized comparison a inverse followed by j commutes with the chosen
signed integral shift. Compose this with the shift compatibility of r. This
proves the desired retained-shift equation for b. No completeness hypothesis or
detection of arbitrary derived morphisms by finite evaluations is used. -/
theorem strictIntegral_coefficientTowerTransport
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n)
    (he : ∀ n : ℕ, FiniteNormalization l E g n (e n))
    (a : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E))
    (ha : ∀ K : PbcCompletedDerived Y (pbcIntegralDatum l E),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K ≫ a.hom.app K =
        (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K) :
    ∃ b : pbcActualStrictCompletedPull (pbcIntegralDatum l E) g ⋙ derived l E X ≅
        finiteTowerLimit l E g C,
      (∀ (P : CochainComplex
          (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ)
        (hP : integralOperationsGoodComplex.{u, u} l E Y ((complexes l E Y).obj P))
        (n : ℕ),
        b.hom.app (DerivedCategory.Q.obj P) ≫ finiteTowerLimitProjection l E g C P n ≫
            DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) =
          (derived l E X).map
            ((completedReductionLimitProjection (pbcIntegralDatum l E) (X := X) n).app
              ((completedTowerPullback g (pbcIntegralDatum l E)).obj
                ((completedReductionTower Y (pbcIntegralDatum l E)).obj
                  (DerivedCategory.Q.obj P))) ≫
              (completedReductionFiniteEvaluation g (pbcIntegralDatum l E) n).hom.app
                (DerivedCategory.Q.obj P)) ≫ finiteComputation l E g P n) ∧
      NatTrans.CommShift (Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ b).hom ℤ := by
  obtain ⟨c, d, hc, hd⟩ := integralPullback_signedShift l E g C
  obtain ⟨r, hr, hs⟩ := integralPullback_roosFiniteTower l E g C c hc d hd
  obtain ⟨i⟩ := pbc_integral_pullback_identification_exists l E g
  obtain ⟨q, hq⟩ := pbc_integral_strict_model_matching_exists l E g i
  let j := strictIntegralRoosTransport l E g q
  refine ⟨j ≪≫ r, ?_, ?_⟩
  · intro P hP n
    change (j.hom.app (DerivedCategory.Q.obj P) ≫ r.hom.app (DerivedCategory.Q.obj P)) ≫
      finiteTowerLimitProjection l E g C P n ≫
        DerivedCategory.Q.map ((finiteComplexComparison l E g n (e n)).app P) = _
    rw [Category.assoc, ← Category.assoc (r.hom.app _), hr P hP n]
    exact strictIntegralRoosTransport_projections l E g hX hY i q hq e he P hP n
  · let _ := d
    have : NatTrans.CommShift r.hom ℤ := hs
    have : NatTrans.CommShift
        (Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ j).hom ℤ :=
      strictIntegralRoosTransport_shifts l E g i q hq c hc d hd a ha
    rw [← Iso.trans_assoc]
    change NatTrans.CommShift
      ((Functor.isoWhiskerRight a.symm (derived l E X) ≪≫ j).hom ≫ r.hom) ℤ
    infer_instance

end WeilConjectures.IntegralCompletedComparison
