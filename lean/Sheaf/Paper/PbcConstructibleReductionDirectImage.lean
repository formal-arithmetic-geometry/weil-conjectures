/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.PbcUniformReductionProfile
public import Sheaf.Paper.CompletedTowerDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.PbcFiniteDirectImageCohomology
import Sheaf.Paper.SbcCompletedOperations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Divisibility.Units
import Mathlib.GroupTheory.OrderOfElement

/-! # Canonical constructible reduction cohomology under proper direct image
Source: blueprint preservation proof, steps 3--4 and 6; Stacks Tags 095U and 0GL0
(blueprint: lem-weil-pbc-constructible-reduction-direct-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

private theorem quotient_orders {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (N : ℕ) (hN : (N : A) ∈ I) (hunit : IsUnit (N : B))
    (n : ℕ) (x : A ⧸ I ^ n) : IsUnit (addOrderOf x : B) := by
  have hz : (N ^ n : ℕ) • x = 0 := by
    have hc : (N ^ n : A ⧸ I ^ n) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), ← map_pow]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [Nat.cast_pow] using Ideal.pow_mem_pow hN n
    simp only [nsmul_eq_mul, Nat.cast_pow, hc, zero_mul]
  have hd : addOrderOf x ∣ N ^ n := addOrderOf_dvd_of_nsmul_eq_zero hz
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (by
    simpa only [Nat.cast_pow] using hunit.pow n)

private theorem annihilator_mem (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (N : ℕ)
    (hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0) :
    (N : PbcIntegralRing l E) ∈ (pbcIntegralDatum l E).ideal := by
  change (N : ULift (Padic.coefficientExtensionIntegers l E)) ∈
    Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  have hi : Padic.coefficientExtensionIdeal l E 1 =
      Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    exact pow_one _
  have hm : (N : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hz : (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1))
        (N : Padic.coefficientExtensionIntegers l E) = 0 := by
      simpa only [map_natCast] using hAnn
    rw [hi] at hz
    exact hz
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  apply Ideal.mem_span_singleton.mpr
  exact ⟨ULift.up a, congrArg ULift.up ha⟩

private theorem lisse_iso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A]
    {F G : pbcModules Y ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (adicLisseConstantRing X A))} (e : F ≅ G)
    (h : IsRelativelyFiniteLisseModule g A F) : IsRelativelyFiniteLisseModule g A G := by
  obtain ⟨S, hS, hs⟩ := h
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := hs V f hf
  exact ⟨M, hM, ⟨((SheafOfModules.overFunctor _ V).mapIso e).symm ≪≫ eM⟩⟩

private theorem constructible_iso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : pbcModules T (adicLisseConstantRing T A)} (e : F ≅ G)
    (h : IsConstructibleProEtaleCoefficientModuleSheaf T A F) :
    IsConstructibleProEtaleCoefficientModuleSheaf T A G := by
  obtain ⟨S, hSn, hSc, hS⟩ := h
  refine ⟨S, hSn, hSc, ?_⟩
  intro i
  exact lisse_iso (S.immersion i) A
    ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing T A)).mapIso e) (hS i)

/-- Proper direct image preserves complete complexes with constructible canonical
reductions, increasing a common upper support bound by twice the fibre dimension.
Source: blueprint preservation proof, steps 3--4 and 6; Stacks Tags 095U and 0GL0
(blueprint: lem-weil-pbc-constructible-reduction-direct-image).

Proof: the annihilator belongs to the uniformizer ideal because it vanishes in
the first quotient. Its (n+1)-st power annihilates every element of the n-th quotient.
Therefore each additive order divides that power of N and is invertible in every
scheme stalk. Apply pbc_finite_directImage_cohomology separately at each quotient.
The canonical perfect projection-formula map is an isomorphism in the actual quotient
module derived category; its homology isomorphisms transport constructibility and the
interval [a,b+2e]. sbcOperations_preserveComplete applies directly to the published
intrinsic completeness predicate. No coefficient-linear lift of an arbitrary map is
used. Empty intervals and zero objects obey the same annihilation and transport proof. -/
theorem pbc_constructible_reduction_directImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (_hDimS : ∃ k : ℕ, topologicalKrullDim S ≤ (k : WithBot ℕ∞))
    (_hDimT : ∃ k : ℕ, topologicalKrullDim T ≤ (k : WithBot ℕ∞))
    (f : S ⟶ T) [IsProper f] (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hInvertS : IsUnit (N : Γ(S, ⊤))) (_hInvertT : IsUnit (N : Γ(T, ⊤)))
    (e : ℕ)
    (_hFib : ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (a b : ℤ) (K : PbcCompletedDerived S (pbcIntegralDatum l E))
    (_hcomplete : PbcIsIntrinsicallyComplete S (pbcIntegralDatum l E) K)
    (_hconstructible : (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf S
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction S (pbcIntegralDatum l E) n).obj K)) K)
    (_hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((pbcCompletedReduction S (pbcIntegralDatum l E) n).obj K))) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      (fun K ↦ ∀ n : ℕ, DerivedCategory.homologyProperty
        (@IsConstructibleProEtaleCoefficientModuleSheaf T
          (PbcQuotient (pbcIntegralDatum l E) n) _
          ((pbcIntegralDatum l E).quotientFinite n))
        ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K))
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
      ∀ (n : ℕ) (q : ℤ), (q < a ∨ b + 2 * (e : ℤ) < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K))) := by
  let d := pbcIntegralDatum l E
  have hmem := annihilator_mem l E N _hAnn
  have horders (V : Scheme.{u}) (hV : IsUnit (N : Γ(V, ⊤))) (n : ℕ)
      (x : PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)) (v : V) :
      IsUnit (addOrderOf x : V.presheaf.stalk v) := by
    apply quotient_orders d.ideal N hmem _ (n + 1) x
    simpa only [map_natCast] using hV.map (V.presheaf.germ ⊤ v trivial).hom
  have hc (n : ℕ) (q : ℤ) := constructible_iso _ _
    (((pbcRestrict (pbcLevelConstantComparison _ d n).hom).mapDerivedCategoryHomologyFunctorIso
          q).app
        ((pbcCompletedReduction _ d n).obj K)).symm (_hconstructible n q)
  refine ⟨?_, ?_, ?_⟩
  · exact (WeilConjectures.sbcOperations_preserveComplete l E f).2 ⟨K, _hcomplete⟩
  · intro n q
    apply constructible_iso _ _
      (((pbcRestrict (pbcLevelConstantComparison _ d n).hom).mapDerivedCategoryHomologyFunctorIso
          q).app
          ((pbcCompletedReduction _ d n).obj _))
    have hfin := pbc_finite_directImage_cohomology _hDimS _hDimT f d n
      (horders S _hInvertS n) (horders T _hInvertT n) e _hFib a b
      ((pbcCompletedReduction S d n).obj K) (hc n) (_hbounded n)
    let := (completedDirectImageProjectionFormula_properties f d).1 n K
    exact constructible_iso T _
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso
          (asIso (completedDirectImageProjectionFormula f d n K)).symm)) (hfin.1 q)
  · intro n q hq
    have hfin := pbc_finite_directImage_cohomology _hDimS _hDimT f d n
      (horders S _hInvertS n) (horders T _hInvertT n) e _hFib a b
      ((pbcCompletedReduction S d n).obj K) (hc n) (_hbounded n)
    let := (completedDirectImageProjectionFormula_properties f d).1 n K
    exact (hfin.2 q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      (asIso (completedDirectImageProjectionFormula f d n K)))

end AlgebraicGeometry.Scheme
