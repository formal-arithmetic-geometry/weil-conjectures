/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.PopescuSeparablePreparationCore
import WeilConjectures.RingTheory.ExistsGeneratorsWithControlledAnnihilators
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.SingularIdeal

/-!
# Preparing the polynomial lifting problem in the separable case

In the positive-dimensional case, the separable Popescu problem is reduced to an auxiliary
problem over the polynomial base `k[x_1, …, x_d]`, with the strict standardness and annihilator
hypotheses needed for eighth-power lifting.

## Implementation details

The exponent `n` is chosen so that the localized `n`th power of `q` lies in the extension of
`H_{A/k}` itself, not merely its radical. The passage from the first/square annihilator
equality to powers is proved by the calling module.

## References

* [Stacks, Tag 07FE] (first two paragraphs of the proof)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The positive-dimensional case admits an auxiliary polynomial-base problem with the
strict standardness and annihilator hypotheses needed for eighth-power lifting. -/
theorem exists_popescu_separable_preparation
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = (d : WithBot ℕ∞))
    (hIq : Ideal.map α.toRingHom (singularIdeal k A) ≤ q.asIdeal)
    (hpow : (q.asIdeal ^ n).map (algebraMap Λ (Localization.AtPrime q.asIdeal)) ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) :
    ∃ (c : ℕ) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ),
      letI := φ.toRingHom.toAlgebra
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
        (_ : Algebra (MvPolynomial (Fin d) k) C)
        (_ : IsScalarTower k (MvPolynomial (Fin d) k) C)
        (_ : FinitePresentation (MvPolynomial (Fin d) k) C)
        (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin d) k] Λ),
        1 ≤ c ∧
        Ideal.span (Set.range (fun i : Fin d ↦
          algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ∧
        (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
        (∀ i : Fin d, algebraMap (MvPolynomial (Fin d) k) Λ
          ((MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c) ∈ q.asIdeal) ∧
        (∀ (i : Fin d)
          (x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin d) k) Λ (MvPolynomial.X j ^ c) ^ 8}),
          (MvPolynomial.X i : MvPolynomial (Fin d) k) • x = 0 ↔
            (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ 2 • x = 0) ∧
        (∀ i : Fin d, IsStrictlyStandardElement (R := MvPolynomial (Fin d) k)
          (algebraMap (MvPolynomial (Fin d) k) C
            ((MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c))) := by
  have _ := hd
  obtain ⟨c, C, instC, instkC, instRC, instTower, instFP, β, hc, hstrict, hlift⟩ :=
    exists_popescu_separable_preparation_core.{u, v, w} (k := k) (A := A) d n hn
  let _ : CommRing C := instC
  let _ : Algebra k C := instkC
  let _ : Algebra (MvPolynomial (Fin d) k) C := instRC
  let _ : IsScalarTower k (MvPolynomial (Fin d) k) C := instTower
  let _ : FinitePresentation (MvPolynomial (Fin d) k) C := instFP
  obtain ⟨π, hgen, hπ, hann⟩ := Ideal.exists_generators_with_controlled_annihilators
    (Ideal.map α.toRingHom (singularIdeal k A)) q.asIdeal hIq n (8 * c) d
    (by omega) (by omega) hpow hdim
  let φ : MvPolynomial (Fin d) k →ₐ[k] Λ := MvPolynomial.aeval π
  let _ := φ.toRingHom.toAlgebra
  obtain ⟨γ, hcomp, hpop⟩ := hlift α φ (by simpa [φ] using hπ)
  refine ⟨c, φ, C, instC, instkC, instRC, instTower, instFP, β, γ,
    hc, ?_, hcomp, hpop, ?_, ?_, hstrict⟩
  · simpa [φ, Localization.AtPrime.map_eq_maximalIdeal] using hgen
  · intro i
    have hi : π i ∈ q.asIdeal := (inferInstance : q.asIdeal.IsPrime).mem_of_pow_mem n (hIq (hπ i))
    change φ (MvPolynomial.X i ^ c) ∈ q.asIdeal
    simpa [φ] using q.asIdeal.pow_mem_of_mem hi c (by omega)
  · intro i
    have heq : (8 * c) = c * 8 := Nat.mul_comm _ _
    have h := Set.ext_iff.mp (hann i)
    simp only [Set.mem_ofPred_eq] at h
    change ∀ x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
      y = φ (MvPolynomial.X j ^ c) ^ 8},
      φ (MvPolynomial.X i) • x = 0 ↔ φ (MvPolynomial.X i ^ 2) • x = 0
    have hJ : Ideal.span {y : Λ | ∃ j : Fin d, j.val < i.val ∧
        y = φ (MvPolynomial.X j ^ c) ^ 8} =
        Ideal.span {y : Λ | ∃ j : Fin d, j < i ∧ y = π j ^ (8 * c)} := by
      congr 1
      ext y
      simp only [φ, map_pow, MvPolynomial.aeval_X, heq, pow_mul, Fin.lt_def]
    rw [hJ]
    simpa only [φ, map_pow, MvPolynomial.aeval_X] using h

end Algebra
