/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete
import Mathlib.Algebra.DualNumber

/-!
# Extending derivations along formally smooth adic maps

An absolute derivation of `R` extends along an `R`-algebra `S` that is `n`-adically complete
and formally smooth for the `n`-adic topology.

## Implementation details

Absolute derivations are represented by `Derivation ℤ`: additivity implies ℤ-linearity, and
the Leibniz identity implies vanishing at one. The proof needs no locality or Noetherian
hypotheses. It uses the dual numbers `A = DualNumber S`, with `R`-algebra structure
`r ↦ φ(r) + ε φ(D r)`, checks that `A` is complete for `n A` with `⋂ (ε S + (n A)^m) = ε S`,
and lifts the identity of `S = A/εS` to a section `σ : S → A` by formal smoothness. Writing
`σ(s) = s + ε D'(s)` gives the extension `D'`.

## References

* [Stacks, Tag 07PL]
* [Stacks, Tag 07NJ]
-/

@[expose] public section

universe u v

private theorem dual_mem_smul {S : Type v} [CommRing S]
    (p : Ideal S) (x : DualNumber S) :
    x ∈ (p • ⊤ : Submodule S (DualNumber S)) ↔ x.fst ∈ p ∧ x.snd ∈ p := by
  constructor
  · intro hx
    constructor
    · have hm := (Submodule.smul_top_le_comap_smul_top p
        (TrivSqZeroExt.fstHom S S S).toLinearMap) hx
      simpa using hm
    · have hm := (Submodule.smul_top_le_comap_smul_top p
        (TrivSqZeroExt.sndHom S S)) hx
      simpa using hm
  · rintro ⟨ha, hb⟩
    have h₁ : TrivSqZeroExt.inl x.fst ∈
        (p • ⊤ : Submodule S (DualNumber S)) := by
      convert Submodule.smul_mem_smul ha
        (Submodule.mem_top : (1 : DualNumber S) ∈ (⊤ : Submodule S (DualNumber S)))
        using 1
      ext <;> simp
    have h₂ : TrivSqZeroExt.inr x.snd ∈
        (p • ⊤ : Submodule S (DualNumber S)) := by
      simpa using Submodule.smul_mem_smul hb
        (Submodule.mem_top : (DualNumber.eps : DualNumber S) ∈
          (⊤ : Submodule S (DualNumber S)))
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    exact (p • ⊤ : Submodule S (DualNumber S)).add_mem h₁ h₂

private theorem dual_complete {S : Type v} [CommRing S]
    (n : Ideal S) [IsAdicComplete n S] :
    IsAdicComplete (n.map (algebraMap S (DualNumber S))) (DualNumber S) := by
  apply (IsAdicComplete.map_algebraMap_iff n (DualNumber S)).mpr
  rw [isAdicComplete_iff]
  constructor
  · refine ⟨?_⟩
    intro x hx
    apply TrivSqZeroExt.ext
    · apply IsHausdorff.haus' (I := n)
      intro m
      have hm := (dual_mem_smul (n ^ m) x).mp (by simpa [SModEq.sub_mem] using hx m)
      simpa [SModEq.sub_mem] using hm.1
    · apply IsHausdorff.haus' (I := n)
      intro m
      have hm := (dual_mem_smul (n ^ m) x).mp (by simpa [SModEq.sub_mem] using hx m)
      simpa [SModEq.sub_mem] using hm.2
  · refine ⟨?_⟩
    intro f hf
    have hc₁ : ∀ {m k : ℕ}, m ≤ k →
        (f m).fst ≡ (f k).fst [SMOD (n ^ m • ⊤ : Submodule S S)] := by
      intro m k hmk
      have hm := (dual_mem_smul (n ^ m) (f m - f k)).mp
        (by simpa [SModEq.sub_mem] using hf hmk)
      simpa [SModEq.sub_mem] using hm.1
    have hc₂ : ∀ {m k : ℕ}, m ≤ k →
        (f m).snd ≡ (f k).snd [SMOD (n ^ m • ⊤ : Submodule S S)] := by
      intro m k hmk
      have hm := (dual_mem_smul (n ^ m) (f m - f k)).mp
        (by simpa [SModEq.sub_mem] using hf hmk)
      simpa [SModEq.sub_mem] using hm.2
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := n) (fun m => (f m).fst) hc₁
    obtain ⟨b, hb⟩ := IsPrecomplete.prec' (I := n) (fun m => (f m).snd) hc₂
    refine ⟨(a, b), fun m => ?_⟩
    rw [SModEq.sub_mem, dual_mem_smul]
    constructor
    · simpa [SModEq.sub_mem] using ha m
    · simpa [SModEq.sub_mem] using hb m

private theorem dual_mem_map {S : Type v} [CommRing S]
    (p : Ideal S) (x : DualNumber S) :
    x ∈ p.map (algebraMap S (DualNumber S)) ↔ x.fst ∈ p ∧ x.snd ∈ p := by
  have he : (p.map (algebraMap S (DualNumber S))).restrictScalars S =
      (p • ⊤ : Submodule S (DualNumber S)) := by
    simp
  change x ∈ (p.map (algebraMap S (DualNumber S))).restrictScalars S ↔ _
  rw [he, dual_mem_smul]

namespace Derivation

/-- An absolute derivation of `R` extends to an absolute derivation of an `R`-algebra `S`
that is `n`-adically complete and formally smooth for the `n`-adic topology. -/
theorem exists_extension_of_formallySmoothAdic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (n : Ideal S) [IsAdicComplete n S] (h : Algebra.FormallySmoothAdic R S n)
    (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r : R, D' (algebraMap R S r) = algebraMap R S (D r) := by
  classical
  let A := DualNumber S
  let I : Ideal A := n.map (algebraMap S A)
  have : IsAdicComplete I A := dual_complete n
  let ψ : R →+* A :=
    { toFun := fun r => (algebraMap R S r, algebraMap R S (D r))
      map_one' := by ext <;> simp [D.map_one_eq_zero]
      map_zero' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp [A]
      map_mul' := by
        intro a b
        ext
        · simp [A]
        · simp [A, D.leibniz, smul_eq_mul, mul_comm] }
  let : Algebra R A := ψ.toAlgebra
  let q : A →ₐ[R] S :=
    { (TrivSqZeroExt.fstHom S S S).toRingHom with commutes' := fun _ => rfl }
  let J : Ideal A := RingHom.ker q.toRingHom
  have hJmem (x : A) : x ∈ J ↔ x.fst = 0 := Iff.rfl
  have hJzero : J ^ 2 = ⊥ := by
    apply le_antisymm _ bot_le
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    have ha' := (hJmem a).mp ha
    have hb' := (hJmem b).mp hb
    apply TrivSqZeroExt.ext <;> simp [A, ha', hb']
  have hJclosed : J = ⨅ (m : ℕ) (_ : 1 ≤ m), J ⊔ I ^ m := by
    apply le_antisymm
    · exact le_iInf fun m => le_iInf fun _ => le_sup_left
    · intro x hx
      apply (hJmem x).mpr
      apply IsHausdorff.haus' (I := n)
      intro k
      have hxk := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hx (k + 1))
        (Nat.succ_le_succ (Nat.zero_le k))
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxk
      have hb' : b.fst ∈ n ^ (k + 1) := by
        exact ((dual_mem_map (n ^ (k + 1)) b).mp
          (by simpa only [I, Ideal.map_pow] using hb)).1
      have hax := (hJmem a).mp ha
      have he : x.fst = b.fst := by
        rw [← hab, TrivSqZeroExt.fst_add, hax, zero_add]
      have hm := Ideal.pow_le_pow_right k.le_succ hb'
      simpa [SModEq.sub_mem, he] using hm
  have hqsurj : Function.Surjective q := fun s => ⟨TrivSqZeroExt.inl s, rfl⟩
  let e : (A ⧸ J) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective hqsurj
  let g : S →ₐ[R] A ⧸ J := e.symm.toAlgHom
  have hge (x : A) : g (q x) = Ideal.Quotient.mk J x := by
    exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply hqsurj x
  have hg : ∀ x ∈ n ^ 1, g x ∈ I.map (Ideal.Quotient.mk J) := by
    intro x hx
    have hin : TrivSqZeroExt.inl x ∈ I := by
      exact Ideal.mem_map_of_mem (algebraMap S A) (by simpa using hx)
    have hmk := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hin
    simpa only [← hge, show q (TrivSqZeroExt.inl x) = x from rfl] using hmk
  obtain ⟨σ, hσ, _⟩ := h.exists_lift_into_complete n I J 2 (by decide)
    (by rw [hJzero]; exact bot_le) hJclosed g 1 (by decide) hg
  have hσfst (s : S) : (σ s).fst = s := by
    have he := congrArg e (AlgHom.congr_fun hσ s)
    change (σ s).fst = e (e.symm s) at he
    simpa only [AlgEquiv.apply_symm_apply] using he
  let dadd : S →+ S :=
    { toFun := fun s => (σ s).snd
      map_zero' := by simp
      map_add' := by intro a b; simp [A] }
  let dlin : S →ₗ[ℤ] S := dadd.toIntLinearMap
  let D' : Derivation ℤ S S := Derivation.mk' dlin (by
    intro a b
    change (σ (a * b)).snd = a * (σ b).snd + b * (σ a).snd
    rw [map_mul, DualNumber.snd_mul, hσfst, hσfst, mul_comm (σ a).snd b])
  refine ⟨D', fun r => ?_⟩
  have he := congrArg TrivSqZeroExt.snd (σ.commutes r)
  exact he

end Derivation
