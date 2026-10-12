/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flat quotients of algebras over an adic completion

Let `I ⊆ A` be a finitely generated ideal, `C` the `I`-adic completion of `A` and `f : C → S` a
ring map such that `A → C → S` is flat. Then for every `n`, `S / Jⁿ S` is flat over `C / Jⁿ`,
where `J = I C` (Stacks, part of the proof of Lemma 0C4G).

## Main results

- `AdicCompletion.ker_evalₐ_eq_map_pow`: the kernel of `C → A / Iⁿ` is `(I C)ⁿ`.
- `AdicCompletion.flat_quotients_of_flat_restriction`
-/

@[expose] public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- For a finitely generated ideal `I`, the kernel of the evaluation `Â → A / Iⁿ` is
`(I Â)ⁿ`. -/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = I.map (algebraMap A (AdicCompletion I A)) ^ n := by
  have h1 : (I ^ n : Ideal A) ≤ I ^ n • ⊤ := by simp
  have h2 : (I ^ n • ⊤ : Ideal A) ≤ I ^ n := by simp
  ext x
  rw [RingHom.mem_ker, ← Ideal.map_pow]
  have hx : x ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I A)) ↔
      x ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  rw [← hx, pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
  constructor
  · intro h
    rw [← factor_evalₐ_eq_eval x h1, h, map_zero]
  · intro h
    rw [← factor_eval_eq_evalₐ x h2, h, map_zero]

/-- The isomorphism `Â / (I Â)ⁿ ≃ A / Iⁿ` induced by evaluation, for finitely generated `I`. -/
noncomputable def quotientMapPowEquiv (hI : I.FG) (n : ℕ) :
    AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)) ^ n ≃+* A ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ_eq_map_pow hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (evalₐ I n).toRingHom) (surjective_evalₐ I n))

lemma quotientMapPowEquiv_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    quotientMapPowEquiv hI n (Ideal.Quotient.mk _ x) = evalₐ I n x :=
  rfl

variable {S : Type*} [CommRing S]

/-- **Flat quotients of a completion algebra whose restriction to the original ring is flat.**
Let `I ⊆ A` be a finitely generated ideal, `C = Â` its `I`-adic completion and `f : C → S` a ring
map such that `A → C → S` is flat. Put `J = I C`. Then for every `n` (including `0`), the
`C / Jⁿ`-module `S / Jⁿ S` is flat.
(blueprint: `lem-weil-pbc-completion-restriction-flat-quotients`) -/
theorem flat_quotients_of_flat_restriction (hI : I.FG) (f : AdicCompletion I A →+* S)
    (hf : (f.comp (algebraMap A (AdicCompletion I A))).Flat) (n : ℕ) :
    letI := f.toAlgebra
    Module.Flat (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)) ^ n)
      (S ⧸ (I.map (algebraMap A (AdicCompletion I A)) ^ n • ⊤ :
        Submodule (AdicCompletion I A) S)) := by
  letI := f.toAlgebra
  set C := AdicCompletion I A
  set J := I.map (algebraMap A C)
  set g := f.comp (algebraMap A C)
  letI := g.toAlgebra
  -- flatness of `A / Iⁿ → S / Iⁿ S`
  have hflatA : (algebraMap (A ⧸ I ^ n) (S ⧸ (I ^ n).map (algebraMap A S))).Flat := by
    have : Module.Flat A S := hf
    have e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (I ^ n)
    have : Module.Flat (A ⧸ I ^ n) (S ⧸ (I ^ n).map (algebraMap A S)) :=
      Module.Flat.of_linearEquiv e.toLinearEquiv
    exact RingHom.flat_algebraMap_iff.mpr this
  have hK : (I ^ n).map (algebraMap A S) = (J ^ n).map (algebraMap C S) := by
    rw [J, ← Ideal.map_pow, Ideal.map_map]
    rfl
  -- flatness of `C / Jⁿ → S / Jⁿ S`
  have hflatC : (algebraMap (C ⧸ J ^ n) (S ⧸ (J ^ n).map (algebraMap C S))).Flat := by
    have hcomp : algebraMap (C ⧸ J ^ n) (S ⧸ (J ^ n).map (algebraMap C S)) =
        ((Ideal.quotEquivOfEq hK).toRingHom.comp
          (algebraMap (A ⧸ I ^ n) (S ⧸ (I ^ n).map (algebraMap A S)))).comp
          (quotientMapPowEquiv hI n).toRingHom := by
      ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      have hx : x - algebraMap A C a ∈ J ^ n := by
        rw [← ker_evalₐ_eq_map_pow hI n, RingHom.mem_ker, map_sub, ← ha,
          AlgHom.commutes, Ideal.Quotient.algebraMap_eq, sub_self]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [quotientMapPowEquiv_mk, ← ha, Ideal.Quotient.algebraMap_quotient_map_quotient,
        Ideal.quotEquivOfEq_mk, Ideal.Quotient.eq]
      refine (Ideal.mem_map_of_mem (algebraMap C S) hx) |> fun h ↦ ?_
      simpa [g, RingHom.algebraMap_toAlgebra] using h
    rw [hcomp]
    exact RingHom.Flat.comp (.of_bijective (quotientMapPowEquiv hI n).bijective)
      (RingHom.Flat.comp hflatA (.of_bijective (Ideal.quotEquivOfEq hK).bijective))
  have : Module.Flat (C ⧸ J ^ n) (S ⧸ (J ^ n).map (algebraMap C S)) :=
    RingHom.flat_algebraMap_iff.mp hflatC
  -- identify the module quotient with the ring quotient
  have hsub : (J ^ n • ⊤ : Submodule C S) = ((J ^ n).map (algebraMap C S)).restrictScalars C :=
    Ideal.smul_top_eq_map _
  let e₀ : (S ⧸ (J ^ n • ⊤ : Submodule C S)) ≃ₗ[C] S ⧸ (J ^ n).map (algebraMap C S) :=
    (Submodule.quotEquivOfEq _ _ hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv C ((J ^ n).map (algebraMap C S)))
  have he₀ (s : S) : e₀ (Submodule.Quotient.mk s) = Ideal.Quotient.mk _ s := rfl
  let e : (S ⧸ (J ^ n • ⊤ : Submodule C S)) ≃ₗ[C ⧸ J ^ n] S ⧸ (J ^ n).map (algebraMap C S) :=
    { e₀ with
      map_smul' := fun r y ↦ by
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply]
        rw [Module.Quotient.mk_smul_mk, he₀, he₀,
          Ideal.Quotient.mk_smul_mk_quotient_map_quotient, Algebra.smul_def] }
  exact Module.Flat.of_linearEquiv e

end AdicCompletion
