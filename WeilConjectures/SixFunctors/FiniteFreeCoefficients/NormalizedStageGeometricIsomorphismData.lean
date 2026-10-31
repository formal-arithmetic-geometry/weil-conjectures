/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Closed.ClosedOpenDualizingMate
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateInvertible
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteBridgeFoundations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageClosedIsomorphismData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomIsomorphismData
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! Geometric stage maps are invertible on ctf objects after normalized scalar change.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem stageAnnihilator
    {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (s : Stage l E) :
    ∃ n : ℕ, (l : s.ring) ^ n = 0 := by
  obtain ⟨e, z, hz, hideal, _⟩ := stage_ramification s
  let n : ℕ := (e : ℕ) * (s.exponent : ℕ)
  have hF := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have hlmem : (l : s.integers) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) := by
    have hgen : Ideal.span
        ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) =
        Padic.coefficientExtensionMaximalIdeal l s.field :=
      hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    rw [hgen]
    apply (hF.2.1 _).mpr
    change spectralNorm (Padic l) s.field (l : s.field) < 1
    rw [← map_natCast (algebraMap (Padic l) s.field) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  refine ⟨n, ?_⟩
  have hm : (l : s.integers) ^ n ∈ s.ideal := by
    change _ ∈ Ideal.span ({s.parameter} : Set s.integers) ^ (s.exponent : ℕ)
    rw [hideal]
    exact Ideal.pow_mem_pow hlmem n
  simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm

private theorem coefficientExponentUnit
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] (n : ℕ) :
    IsUnit ((l ^ n : ℕ) : Γ(T, ⊤)) := by
  have hnonzero : (l : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : l.Prime) hlp.symm
  have hu : IsUnit ((l ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hnonzero)
  let r : k →+* Γ(T, ⊤) :=
    (T ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using hu.map r

private theorem stageInvertibleExponent
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] [Fact l.Prime] (hlp : l ≠ p)
    {E : Type (u + 1)} [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (s : Stage l E)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] : HasInvertibleExponent s.ring T := by
  obtain ⟨n, hn⟩ := stageAnnihilator s
  exact ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos _, by simpa using hn,
    coefficientExponentUnit k p l hlp T n⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
end WeilConjectures.FiniteFreeCoefficients
