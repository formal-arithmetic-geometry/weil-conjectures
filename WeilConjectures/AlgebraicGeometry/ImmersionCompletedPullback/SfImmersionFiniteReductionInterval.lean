/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackCoreA
import WeilConjectures.ProperBaseChange.IntegralPullbackIdentificationExists
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralReductionHomology
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteImmersionConstructibilityInterval

/-! # Finite reductions of ordinary immersion pullback

Source: localization Step 6, finite constructibility; Stacks Tags 09AK, 09AL and 09B5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme.ImmersionCompletedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private theorem coefficientIso_eq (T : Scheme.{u}) :
    (adicLisseForget T).mapIso (completedRingIso l E T) =
      integralDetailedCoefficientComparison T l E := by
  apply (integralDetailedCoefficientComparison_exists T l E).unique
    ?_ (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  intro n
  have hq : quotientEquiv l E n = integralCoefficientULift l E n :=
    (quotientEquiv_exists l E n).unique
      (quotientEquiv_exists l E n).exists.choose_spec
      (integralCoefficientULift_exists l E n).exists.choose_spec
  have h := congrArg ((adicLisseForget T).map)
    ((completedRingIso_exists l E T).exists.choose_spec n)
  have hp : (adicLisseForget T).map
      (completedIntegralCommRingProjectionUnrestricted l E T n) =
      limit.π (integralCoefficientSheafSystem l E T) (op n) := by
    apply Sheaf.hom_ext
    ext U x
    rfl
  simpa only [Functor.map_comp, hp, Functor.mapIso_hom, completedRingIso,
    finiteRingIso, integralDetailedLevelComparison, hq] using h

private theorem back_eq (T : Scheme.{u}) :
    integralDetailedTransport T l E = pbcDerivedRestrict (completedRingIso l E T).hom := by
  have h := congrArg Iso.hom (coefficientIso_eq l E T)
  have := (integralDetailedCoefficientRestriction_exact T l E).1
  have := (integralDetailedCoefficientRestriction_exact T l E).2
  dsimp only [integralDetailedTransport, pbcDerivedRestrict, pbcRestrict]
  simp only [← h]
  rfl

private def roundTripCompleted (T : Scheme.{u}) :
    transport l E T ⋙ integralDetailedTransport T l E ≅ 𝟭 _ := by
  rw [back_eq l E T]
  let e := Classical.choice
    (IntegralCoefficientPresentation.restrict_equivalence (completedRingIso l E T)).2.2.2
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private def roundTripDetailed (T : Scheme.{u}) :
    integralDetailedTransport T l E ⋙ transport l E T ≅ 𝟭 _ := by
  rw [back_eq l E T]
  let e := Classical.choice
    (IntegralCoefficientPresentation.restrict_equivalence (completedRingIso l E T)).2.2.1
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private def ordinaryComparison
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) ≅
      (ordinaryIntegralDerivedPull l E f).obj ((transport l E X).obj K) := by
  let C := Classical.choice (pbc_integral_pullback_identification_exists l E f)
  exact (transport l E Y).mapIso
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).mapIso
        ((roundTripCompleted l E X).app K).symm ≪≫
      (C.derivedIso.app ((transport l E X).obj K)).symm) ≪≫
    (roundTripDetailed l E Y).app _

/-- One finite reduction retains constructibility and the given interval under pullback.
Source: localization Step 6, last paragraph, and Stacks Tags 09AK, 09AL and 09B5
(blueprint: lem-sf-immersion-finite-reduction-interval).

Proof: identify the two quotient coefficient rings by quotientEquiv and the completed
coefficients by completedRingIso, retaining their projection equations. The scalar
extension adjunctions then identify detailed reduction of transport with the canonical
finite reduction of the adic datum. Compose this identification with finiteComparison:
the target reduction is the exact inverse image of the source reduction, up to these
coefficient equivalences. Exact coefficient restriction preserves and reflects zero
cohomology and finite locally constant module sheaves on every stratum. Exact inverse
image commutes with cohomology; pull back the finite locally closed stratification of
each source cohomology sheaf and its finite constant local models. Thus each target
cohomology sheaf is constructible. In every degree outside [r,s] the source cohomology
is zero, hence so is its inverse image. The target support is therefore contained in
the same interval, which is finite; this also supplies the finite-support clause of
intrinsicFiniteTorsionConstructible. This argument uses no Noetherian assumption and
includes the zero complex, an empty interval, the empty scheme, and identity immersion.
-/
theorem finite_reduction_preservesConstructibleInterval [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) (r s : ℤ)
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj ((transport l E X).obj K)) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj ((transport l E X).obj K)) ⊆
          Set.Icc r s) :
    intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
        Set.Icc r s := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let KX := (scalarReductionDerivedExtension.{u, u} l E X n).obj
    ((transport l E X).obj K)
  let KY := (scalarReductionDerivedExtension.{u, u} l E Y n).obj
    ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))
  have hH (q : ℤ) : Nonempty ((DerivedCategory.homologyFunctor _ q).obj KY ≅
      proEtaleConstantModulePullback f A
        ((DerivedCategory.homologyFunctor _ q).obj KX)) := by
    obtain ⟨e⟩ := ordinaryIntegralReductionHomology l E f
      ((transport l E X).obj K) n q
    exact ⟨(DerivedCategory.homologyFunctor _ q).mapIso
      ((scalarReductionDerivedExtension.{u, u} l E Y n).mapIso
        (ordinaryComparison l E f K)) ≪≫ e⟩
  have hs : proEtaleCohomologicalSupport KY ⊆ Set.Icc r s := by
    intro q hq
    apply hK.2
    intro hz
    obtain ⟨e⟩ := hH q
    exact hq (((proEtaleConstantRingPullback A f).map_isZero hz).of_iso e)
  refine ⟨⟨(Set.finite_Icc r s).subset hs, ?_⟩, hs⟩
  intro q
  obtain ⟨e⟩ := hH q
  exact constructible_of_iso A e
    (pullback_constructible A f _ (hK.1.2 q))

end AlgebraicGeometry.Scheme.ImmersionCompletedPullback
