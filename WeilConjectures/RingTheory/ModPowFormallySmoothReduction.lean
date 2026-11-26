/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Transport of formal smoothness to an iterated prime-power quotient

If `ZMod (p^m) → Λ/(p^m)` is formally smooth and `n ≤ m`, then `ZMod (p^n) → Λ/(p^n)` is formally
smooth; this is the quotient identification in an induction step.

## Implementation details

With `R = ZMod (p^m)`, `S = Λ/(p^m)` and `I = (p^n)`, the third isomorphism theorem identifies
`S/IS` with `Λ/(p^n)` and `R/I` with `ZMod (p^n)`, compatibly with the integer-cast maps, and
formal smoothness is transported along these isomorphisms.

## References

* [Stacks, Tag 0329]
-/

@[expose] public section

universe u

/-- The quotient identification in the induction step of the construction of Cohen rings:
formal smoothness modulo `p^m` gives formal smoothness modulo `p^n` for `n ≤ m`. No flatness or
Cohen-ring hypothesis is used here. -/
theorem modPow_formallySmooth_reduction
    (p : ℕ) (Λ : Type u) [CommRing Λ] (n m : ℕ) (hnm : n ≤ m)
    [Algebra (ZMod (p ^ m)) (Λ ⧸ Ideal.span {(p : Λ) ^ m})]
    (ih : ∀ [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})],
      Algebra.FormallySmooth (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})) :
    let I : Ideal (ZMod (p ^ m)) := Ideal.span {((p : ZMod (p ^ m)) ^ n)}
    let J := I.map (algebraMap (ZMod (p ^ m)) (Λ ⧸ Ideal.span {(p : Λ) ^ m}))
    (Ideal.quotientMap J
      (algebraMap (ZMod (p ^ m)) (Λ ⧸ Ideal.span {(p : Λ) ^ m}))
      Ideal.le_comap_map).FormallySmooth := by
  let R := ZMod (p ^ m)
  let S := Λ ⧸ Ideal.span {(p : Λ) ^ m}
  let I : Ideal R := Ideal.span {((p : R) ^ n)}
  let J := I.map (algebraMap R S)
  let q : R →+* ZMod (p ^ n) := ZMod.castHom (pow_dvd_pow p hnm) _
  have hker : RingHom.ker q = I := by
    apply le_antisymm
    · intro x hx
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
      have hz : ((p ^ n : ℕ) : ℤ) ∣ z := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ n)).mp
        simpa [q, R, RingHom.mem_ker] using hx
      obtain ⟨a, rfl⟩ := hz
      apply Ideal.mem_span_singleton.mpr
      exact ⟨(a : R), by simp⟩
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      simp [RingHom.mem_ker, q, ← Nat.cast_pow]
  let eR : (R ⧸ I) ≃+* ZMod (p ^ n) :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective (ZMod.castHom_surjective _))
  let K : Ideal Λ := Ideal.span {(p : Λ) ^ m}
  let L : Ideal Λ := Ideal.span {(p : Λ) ^ n}
  have hKL : K ≤ L := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact pow_dvd_pow (p : Λ) hnm
  have hJ : J = L.map (Ideal.Quotient.mk K) := by
    simp [J, I, L, K, R, S, Ideal.map_span, Set.image_singleton]
  let eS : (S ⧸ J) ≃+* (Λ ⧸ L) :=
    (Ideal.quotEquivOfEq hJ).trans (DoubleQuot.quotQuotEquivQuotOfLE hKL)
  let gZ : ℤ →+* (Λ ⧸ L) := Int.castRingHom _
  have hkZ : Ideal.span {((p ^ n : ℕ) : ℤ)} ≤ RingHom.ker gZ := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change gZ ((p ^ n : ℕ) : ℤ) = 0
    simp only [gZ, Int.coe_castRingHom, Nat.cast_pow, Int.cast_pow, Int.cast_natCast]
    exact (map_pow (Ideal.Quotient.mk L) (p : Λ) n) ▸
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let g : ZMod (p ^ n) →+* (Λ ⧸ L) :=
    (Ideal.Quotient.lift _ gZ hkZ).comp
      (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  let : Algebra (ZMod (p ^ n)) (Λ ⧸ L) := g.toAlgebra
  have hg : g.FormallySmooth := ih
  have hcomp := ((RingHom.FormallySmooth.of_bijective
      (f := eR.toRingHom) eR.bijective).comp hg).comp
    (RingHom.FormallySmooth.of_bijective (f := eS.symm.toRingHom) eS.symm.bijective)
  have heq : eS.symm.toRingHom.comp (g.comp eR.toRingHom) =
      Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun f : R →+* S ⧸ J ↦ f y)
      (RingHom.ext_zmod
        ((eS.symm.toRingHom.comp (g.comp eR.toRingHom)).comp (Ideal.Quotient.mk I))
        ((Ideal.quotientMap J (algebraMap R S) Ideal.le_comap_map).comp
          (Ideal.Quotient.mk I)))
  rw [heq] at hcomp
  exact hcomp
