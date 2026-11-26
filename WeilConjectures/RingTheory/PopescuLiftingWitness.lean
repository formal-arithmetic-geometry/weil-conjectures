/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.PopescuLifting
import WeilConjectures.RingTheory.PopescuLiftingWitnessControl

/-!
# The lifting witness in Popescu's desingularization lemma

Applying the Popescu lifting lemma with `π⁴` gives the finitely presented algebra `D`, the
compatible fourth-power quotient map, and the comparison of singular ideals needed for the
final desingularization step of Stacks Lemma 07F0.

## Implementation details

No strict standardness hypothesis or factorization through a desingularized algebra is asserted
here. The argument uses no nontriviality assumption: if `π` is a unit the relevant quotients
are zero, and if `π` is nilpotent the smooth locus away from `π` is empty.

## References

* [Stacks, Tag 07CP] (applied with `π ^ 4`)
* [Stacks, Tag 07F0] (the prime-ideal verification)
-/

@[expose] public section
universe u v w z
namespace Algebra

/-- Equal annihilators of the first two powers give equal annihilators of powers four
and eight. -/
private theorem annihilator_four_eight (T : Type*) [CommRing T] (p : T)
    (h : Module.annihilator T (Ideal.span ({p} : Set T)) =
      Module.annihilator T (Ideal.span ({p ^ 2} : Set T))) :
    Module.annihilator T (Ideal.span ({p ^ 4} : Set T)) =
      Module.annihilator T (Ideal.span ({p ^ 8} : Set T)) := by
  have hb (x : T) : x * p ^ 2 = 0 ↔ x * p = 0 := by
    have he := SetLike.ext_iff.mp h x
    change x ∈ (Ideal.span ({p} : Set T)).annihilator ↔
      x ∈ (Ideal.span ({p ^ 2} : Set T)).annihilator at he
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using he.symm
  have hn (n : ℕ) : ∀ x : T, x * p ^ (n + 1) = 0 ↔ x * p = 0 := by
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [show x * p ^ (n + 1 + 1) = (x * p) * p ^ (n + 1) by ring,
        ih, mul_assoc, ← pow_two]
      exact hb x
  ext x
  change x ∈ (Ideal.span ({p ^ 4} : Set T)).annihilator ↔
    x ∈ (Ideal.span ({p ^ 8} : Set T)).annihilator
  simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact (hn 3 x).trans (hn 7 x).symm

/-- The lifting part of Stacks 07F0, before desingularization. It provides the
compatible fourth-power quotient map, the singular-ideal element, and the comparison
of singular ideals needed by the final application of 07CT. -/
theorem popescu_lifting_witness
    (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R]
    (π : R)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (hAnnΛ : Module.annihilator Λ (Ideal.span ({algebraMap R Λ π} : Set Λ)) =
      Module.annihilator Λ (Ideal.span ({(algebraMap R Λ π) ^ 2} : Set Λ)))
    (α : A →ₐ[R] Λ) [FinitePresentation R A]
    (C : Type z) [CommRing C]
    [Algebra (R ⧸ Ideal.span ({π ^ 8} : Set R)) C]
    [FinitePresentation (R ⧸ Ideal.span ({π ^ 8} : Set R)) C]
    (σ : (A ⧸ Ideal.map (algebraMap R A) (Ideal.span ({π ^ 8} : Set R)))
      →ₐ[R ⧸ Ideal.span ({π ^ 8} : Set R)] C)
    (τ : C →ₐ[R ⧸ Ideal.span ({π ^ 8} : Set R)]
      (Λ ⧸ Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R))))
    (hfactor : ∀ a : A,
      τ (σ (Ideal.Quotient.mk
        (Ideal.map (algebraMap R A) (Ideal.span ({π ^ 8} : Set R))) a)) =
        Ideal.Quotient.mk
          (Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R))) (α a)) :
    ∃ (D : Type (max u z)) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧ ∃ (δ : D →ₐ[R] Λ),
        (∃ φ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
            (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
          ∀ (a : A) (d : D),
            φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
            Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
              Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d)) ∧
        algebraMap R D π ∈ singularIdeal R D ∧
        Ideal.map τ.toRingHom (singularIdeal (R ⧸ Ideal.span ({π ^ 8} : Set R)) C) ≤
          Ideal.map
            (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R))))
            (Ideal.map δ.toRingHom (singularIdeal R D)).radical := by
  have hp8 : (π ^ 4) ^ 2 = π ^ 8 := by rw [← pow_mul]
  have hmap8 : Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R)) =
      Ideal.span ({algebraMap R Λ (π ^ 8)} : Set Λ) := by
    rw [Ideal.map_span, Set.image_singleton]
  let : Algebra R C := ((algebraMap (R ⧸ Ideal.span ({π ^ 8} : Set R)) C).comp
    (Ideal.Quotient.mk _)).toAlgebra
  have : IsScalarTower R (R ⧸ Ideal.span ({π ^ 8} : Set R)) C :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have lift := @popescu_lifting R Λ C _ _ _ _ _ _ (π ^ 4)
    (by rw [hp8]; exact annihilator_four_eight R π hAnnR)
    (by
      rw [hp8, map_pow, map_pow]
      exact annihilator_four_eight Λ (algebraMap R Λ π) hAnnΛ)
  rw [hp8, ← hmap8] at lift
  let j := τ.restrictScalars R
  obtain ⟨D, iD, iRD, δ, ψ, red, c, cmod, hfp, hψ, hred, hc,
      _hcmod, haway, hover, _hrelative⟩ := @lift inferInstance inferInstance inferInstance j
  let : CommRing D := iD
  let : Algebra R D := iRD
  let : FinitePresentation R D := hfp
  revert ψ red c cmod haway
  rw [map_pow (algebraMap R D), map_pow (algebraMap R Λ) π 4]
  intro ψ red c cmod hψ hred hc _hcmod haway hover _hrelative
  have hπ : algebraMap R D π ∈ singularIdeal R D := by
    rw [← (singularIdeal_isRadical R D).radical, Ideal.radical_eq_sInf]
    apply Ideal.mem_sInf.mpr
    rintro p ⟨hp, hprime⟩
    by_contra hn
    have hs := haway ⟨p, hprime⟩ (fun hpow ↦ hn (hprime.mem_of_pow_mem 4 hpow))
    have hz : (⟨p, hprime⟩ : PrimeSpectrum D) ∈
        PrimeSpectrum.zeroLocus (singularIdeal R D : Set D) := hp
    rw [(singularIdeal_zeroLocus R D).1] at hz
    exact hz hs
  let β : A →ₐ[R] C := (σ.restrictScalars R).comp
    (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R A) (Ideal.span ({π ^ 8} : Set R))))
  let f := c.comp β
  have hkill : ∀ a ∈ Ideal.span {(algebraMap R A π) ^ 4}, f a = 0 := by
    change Ideal.span {(algebraMap R A π) ^ 4} ≤ RingHom.ker f.toRingHom
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    calc
      f ((algebraMap R A π) ^ 4) =
          Ideal.Quotient.mk _ ((algebraMap R D π) ^ 4) := by
        simp only [map_pow, f.commutes, Ideal.Quotient.mk_algebraMap]
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  let φ := Ideal.Quotient.liftₐ _ f hkill
  refine ⟨D, iD, iRD, hfp, δ, ⟨φ, ?_⟩, hπ, ?_⟩
  · intro a d had
    have hfa : f a = Ideal.Quotient.mk _ d := had
    have hcompat : ψ (f a) = Ideal.Quotient.mk _ (α a) := by
      change (ψ.comp c.toRingHom) (β a) = _
      rw [hc]
      change red (j (β a)) = _
      have hj : j (β a) = Ideal.Quotient.mk
          (Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R))) (α a) := by
        exact hfactor a
      rw [hj]
      exact DFunLike.congr_fun hred (α a)
    have hd : ψ (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (δ d) :=
      DFunLike.congr_fun hψ d
    exact hcompat.symm.trans ((congrArg ψ hfa).trans hd)
  · have hL : Ideal.span ({(algebraMap R Λ π) ^ 4} : Set Λ) ≤
        (Ideal.map δ.toRingHom (singularIdeal R D)).radical := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      have hm := Ideal.mem_map_of_mem δ.toRingHom hπ
      change δ (algebraMap R D π) ∈ Ideal.map δ.toRingHom (singularIdeal R D) at hm
      rw [δ.commutes] at hm
      exact Ideal.le_radical
        ((Ideal.map δ.toRingHom (singularIdeal R D)).pow_mem_of_mem hm 4 (by decide))
    have ht := popescu_lifting_witness_control R
      (R ⧸ Ideal.span ({π ^ 8} : Set R)) C D Λ
      (Ideal.span {(algebraMap R D π) ^ 4})
      (Ideal.map (algebraMap R Λ) (Ideal.span ({π ^ 8} : Set R)))
      (Ideal.span {(algebraMap R Λ π) ^ 4}) δ.toRingHom ψ red c.toRingHom
      j.toRingHom hψ hred hc hL hover
    exact ht

end Algebra
