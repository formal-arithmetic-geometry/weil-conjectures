/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Reduction of the completed module along an extended ideal

For a ring map `φ : R → S` and a finitely generated ideal `I` of `R` with `S/IS` finite over
`R/I`, the reduction of the `IS`-adic completion of `S` modulo `I` is finite over the reduction
of the `I`-adic completion of `R`.

## Implementation details

The `IS`-adic completion of `S` is identified with the `I`-adic completion of the `R`-module `S`,
and the coordinate hypothesis on `ψ` identifies its action with the canonical completed-base
action. Both reductions are then identified with `S/IS` over `R/I` by [Stacks, Tag 05GG], and the
given generators are transported. No local or Noetherian hypothesis is used.

## References

* [Stacks, Tag 0394], last paragraph of the proof
* [Stacks, Tag 031D]
* [Stacks, Tag 05GG]
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- The reduction of the completion for an extended ideal is finite over the reduced
completed base when the original reduction is finite. -/
theorem extendedCompletion_module_reduction
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (I : Ideal R) (φ : R →+* S) (hI : I.FG)
    (hfinite : letI := (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).toAlgebra
      Module.Finite (R ⧸ I) (S ⧸ Ideal.map φ I))
    (ψ : AdicCompletion I R →+* AdicCompletion (Ideal.map φ I) S)
    (hψ : ∀ (k : ℕ) (x : AdicCompletion I R) (r : R),
      AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r →
      AdicCompletion.evalₐ (Ideal.map φ I) k (ψ x) =
        Ideal.Quotient.mk ((Ideal.map φ I) ^ k) (φ r)) :
    letI := ψ.toAlgebra
    let K := I.map (algebraMap R (AdicCompletion I R))
    Module.Finite (AdicCompletion I R ⧸ K)
        (AdicCompletion (Ideal.map φ I) S ⧸
          (K • ⊤ : Submodule (AdicCompletion I R) (AdicCompletion (Ideal.map φ I) S))) := by
  let := ψ.toAlgebra
  let A := AdicCompletion I R
  let J := Ideal.map φ I
  let B := AdicCompletion J S
  let K := I.map (algebraMap R A)
  let q := Ideal.quotientMap J φ Ideal.le_comap_map
  let e := (evalOneₐ J).toRingHom
  have hbase : ψ.comp (algebraMap R A) = (algebraMap S B).comp φ := by
    apply RingHom.ext
    intro r
    apply ext_evalₐ
    intro k
    change evalₐ J k (ψ (of I R r)) = evalₐ J k (of J S (φ r))
    rw [evalₐ_of]
    exact hψ k (of I R r) r (evalₐ_of I k r)
  have hres : e.comp ψ = q.comp (evalOneₐ I).toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 x)
    have hx := hψ 1 x r hr.symm
    change evalₐ J 1 (ψ x) = Ideal.Quotient.mk (J ^ 1) (φ r) at hx
    have hx' := congrArg (Ideal.Quotient.factor (show J ^ 1 ≤ J by simp)) hx
    have hr' := congrArg (Ideal.Quotient.factor (show I ^ 1 ≤ I by simp)) hr
    change e (ψ x) = q ((evalOneₐ I) x)
    simp only [factorₐ_evalₐ_one, Ideal.Quotient.factor_mk] at hr'
    rw [← hr']
    change evalOneₐ J (ψ x) = Ideal.Quotient.mk J (φ r)
    simpa only [factorₐ_evalₐ_one, Ideal.Quotient.factor_mk] using hx'
  have hfin : (e.comp ψ).Finite := by
    rw [hres]
    exact RingHom.Finite.comp (show q.Finite from hfinite)
      (RingHom.Finite.of_surjective _ (evalOneₐ_surjective I))
  let := (e.comp ψ).toAlgebra
  let : Module.Finite A (S ⧸ J) := hfin
  let f : B →ₗ[A] S ⧸ J :=
    { e.toAddMonoidHom with
      map_smul' := fun a b ↦ by
        change e (ψ a * b) = (e.comp ψ) a * e b
        exact e.map_mul _ _ }
  have hmap : K.map ψ = J.map (algebraMap S B) := by
    dsimp [K, J]
    rw [Ideal.map_map, Ideal.map_map, hbase]
  have hker : (K • ⊤ : Submodule A B) = f.ker := by
    rw [Ideal.smul_top_eq_map]
    change (K.map ψ).restrictScalars A = f.ker
    rw [hmap, ← ker_evalOneₐ_eq_map J (hI.map φ)]
    rfl
  have hfiniteA : Module.Finite A (B ⧸ (K • ⊤ : Submodule A B)) := by
    rw [hker]
    exact Module.Finite.equiv (f.quotKerEquivOfSurjective (evalOneₐ_surjective J)).symm
  let := hfiniteA
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ K) _

end AdicCompletion
