/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # The explicit corrected polynomial quotient and its reduction

The corrected quotient `A'` of a presentation, obtained by replacing each equation `gᵢ` by
`gᵢ - ∑ εᵢⱼ δᵢⱼ` with `εᵢⱼ ∈ I` and new variables `δᵢⱼ`, satisfies `A' / I A' ≅ Bbar[δᵢⱼ]`.

## Implementation details

Modulo `I` every `εᵢⱼ` vanishes, and the universal properties of polynomial rings and quotients
give mutually inverse maps. `ULift` merely relabels the correction variables. Empty sets and the
zero algebra are allowed; no assumption on `I²` or smoothness is used.

## References

* [Stacks, Tag 07CK]
-/

@[expose] public section

universe u w d

namespace Algebra

variable (R : Type u) [CommRing R] (A : Type w) [CommRing A] [Algebra R A]
variable (I : Ideal R) (n m : ℕ) (N : Fin m → ℕ)
variable (g : Fin m → MvPolynomial (Fin n) A) (ε : (i : Fin m) → Fin (N i) → I)

/-- Variables of the corrected presentation. The `ULift` sets the carrier universe
without changing the finite set of variables. -/
abbrev PopescuCorrectionVariables := Fin n ⊕ ULift.{d} (Σ i : Fin m, Fin (N i))

/-- The equation `gᵢ - ∑ εᵢⱼ δᵢⱼ`, with genuine polynomial data. -/
noncomputable def popescuCorrectionRelation (i : Fin m) :
    MvPolynomial (PopescuCorrectionVariables.{d} n m N) A :=
  MvPolynomial.rename Sum.inl (g i) -
    ∑ j, MvPolynomial.C (algebraMap R A (ε i j)) *
      MvPolynomial.X (Sum.inr (ULift.up ⟨i, j⟩))

/-- The finitely generated ideal of the corrected equations. -/
noncomputable def popescuCorrectionIdeal :
    Ideal (MvPolynomial (PopescuCorrectionVariables.{d} n m N) A) :=
  Ideal.span (Set.range (popescuCorrectionRelation.{u, w, d} R A I n m N g ε))

/-- The corrected quotient, constructed independently of any existence theorem. -/
abbrev PopescuCorrectionQuotient :=
  MvPolynomial (PopescuCorrectionVariables.{d} n m N) A ⧸
    popescuCorrectionIdeal.{u, w, d} R A I n m N g ε

/-- Reduction of the explicit corrected quotient identifies it with a polynomial
extension of the quotient by the uncorrected reduced equations. -/
theorem nonempty_popescuCorrectionQuotient_reduction_equiv :
    Nonempty
      ((PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε ⧸
        I.map (algebraMap R (PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε))) ≃ₐ[R ⧸ I]
        MvPolynomial (ULift.{d} (Σ i : Fin m, Fin (N i)))
          (MvPolynomial (Fin n) (A ⧸ I.map (algebraMap R A)) ⧸
            Ideal.span (Set.range fun i ↦
              MvPolynomial.map (Ideal.Quotient.mk (I.map (algebraMap R A))) (g i)))) := by
  classical
  let K := popescuCorrectionIdeal.{u, w, d} R A I n m N g ε
  let J := I.map (algebraMap R (PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε))
  let IA := I.map (algebraMap R A)
  let kA := Ideal.Quotient.mk IA
  let L : Ideal (MvPolynomial (Fin n) (A ⧸ IA)) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map kA (g i))
  let kB := Ideal.Quotient.mk L
  let q := (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk K)
  have q_surj : Function.Surjective q :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have qI (r : R) (hr : r ∈ I) : q (MvPolynomial.C (algebraMap R A r)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change algebraMap R (PopescuCorrectionQuotient.{u, w, d} R A I n m N g ε) r ∈ J
    exact Ideal.mem_map_of_mem _ hr
  -- Construct the reverse map, first on reduced coefficients and old variables.
  let a := q.comp MvPolynomial.C
  have aIA : IA ≤ RingHom.ker a := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact qI r hr
  let a' := Ideal.Quotient.lift IA a (fun r hr ↦ aIA hr)
  let b0 := MvPolynomial.eval₂Hom a' (fun i : Fin n ↦ q (MvPolynomial.X (Sum.inl i)))
  have b0_map (p : MvPolynomial (Fin n) A) :
      b0 (MvPolynomial.map kA p) = q (MvPolynomial.rename Sum.inl p) := by
    have hh : b0.comp (MvPolynomial.map kA) =
        q.comp (MvPolynomial.rename Sum.inl).toRingHom := by
      apply MvPolynomial.ringHom_ext <;> intro r <;> simp [b0, a', a, kA]
    exact RingHom.congr_fun hh p
  have b0L : L ≤ RingHom.ker b0 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change b0 (MvPolynomial.map kA (g i)) = 0
    rw [b0_map]
    have hrel : q (popescuCorrectionRelation.{u, w, d} R A I n m N g ε i) = 0 := by
      have hk : popescuCorrectionRelation.{u, w, d} R A I n m N g ε i ∈ K :=
        Ideal.subset_span ⟨i, rfl⟩
      change Ideal.Quotient.mk J (Ideal.Quotient.mk K _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hk, map_zero]
    simpa [popescuCorrectionRelation, map_sub, map_sum, map_mul, qI] using hrel
  let b := Ideal.Quotient.lift L b0 (fun p hp ↦ b0L hp)
  let h := MvPolynomial.eval₂Hom b
    (fun j : ULift.{d} (Σ i : Fin m, Fin (N i)) ↦ q (MvPolynomial.X (Sum.inr j)))
  -- Construct the forward map and descend through both quotient ideals.
  let c : A →+* MvPolynomial (ULift.{d} (Σ i : Fin m, Fin (N i)))
      (MvPolynomial (Fin n) (A ⧸ IA) ⧸ L) :=
    MvPolynomial.C.comp (kB.comp (MvPolynomial.C.comp kA))
  let f0 := MvPolynomial.eval₂Hom c
    (Sum.elim (fun i ↦ MvPolynomial.C (kB (MvPolynomial.X i))) MvPolynomial.X)
  have f0_rename (p : MvPolynomial (Fin n) A) :
      f0 (MvPolynomial.rename Sum.inl p) = MvPolynomial.C (kB (MvPolynomial.map kA p)) := by
    have hh : f0.comp (MvPolynomial.rename Sum.inl).toRingHom =
        MvPolynomial.C.comp (kB.comp (MvPolynomial.map kA)) := by
      apply MvPolynomial.ringHom_ext <;> intro r <;> simp [f0, c]
    exact RingHom.congr_fun hh p
  have cI (r : R) (hr : r ∈ I) : c (algebraMap R A r) = 0 := by
    have hz : kA (algebraMap R A r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    change MvPolynomial.C (kB (MvPolynomial.C (kA _))) = 0
    rw [hz, map_zero, map_zero, map_zero]
  have cε (i : Fin m) (j : Fin (N i)) : c (algebraMap R A (ε i j)) = 0 :=
    cI _ (ε i j).property
  have f0K : K ≤ RingHom.ker f0 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f0 (popescuCorrectionRelation.{u, w, d} R A I n m N g ε i) = 0
    have hz : kB (MvPolynomial.map kA (g i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp [popescuCorrectionRelation, map_sub, map_sum, map_mul, f0_rename, f0, cε, hz]
  let fQ := Ideal.Quotient.lift K f0 (fun p hp ↦ f0K hp)
  have fQJ : J ≤ RingHom.ker fQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change fQ (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R A r))) = 0
    simpa [fQ, f0] using cI r hr
  let f := Ideal.Quotient.lift J fQ (fun x hx ↦ fQJ hx)
  have fq (p : MvPolynomial (PopescuCorrectionVariables.{d} n m N) A) :
      f (q p) = f0 p := by
    simp only [f, q, RingHom.comp_apply, Ideal.Quotient.lift_mk]
    exact Ideal.Quotient.lift_mk K f0 _
  -- The composites fix coefficients, old variables and correction variables.
  have ha (r : A) : h (c r) = a r := by simp [h, c, b, b0, a', kA, kB]
  have hf0 : h.comp f0 = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [f0, a] using ha r
    · intro i
      rcases i with i | j
      · simp [f0, h, b, b0, kB]
      · simp [f0, h]
  have hf : h.comp f = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := q_surj x
    simpa only [RingHom.comp_apply, RingHom.id_apply, fq] using RingHom.congr_fun hf0 p
  have fb0 : f.comp b0 = MvPolynomial.C.comp kB := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [b0, a', a, fq, f0, c, kA]
    · intro i
      simp [b0, fq, f0]
  have fb : f.comp b = MvPolynomial.C := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro p
    simpa [b, kB, RingHom.comp_apply] using RingHom.congr_fun fb0 p
  have fh : f.comp h = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [h] using RingHom.congr_fun fb r
    · intro j
      simp [h, fq, f0]
  let e := RingEquiv.ofRingHom f h fh hf
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_⟩
  -- Check R/I-linearity on representatives from R.
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change f (q (MvPolynomial.C (algebraMap R A r))) = _
  rw [fq]
  simp only [f0, MvPolynomial.eval₂Hom_C]
  change MvPolynomial.C (kB (MvPolynomial.C (kA (algebraMap R A r)))) = _
  rw [MvPolynomial.algebraMap_apply]
  congr 1

end Algebra
