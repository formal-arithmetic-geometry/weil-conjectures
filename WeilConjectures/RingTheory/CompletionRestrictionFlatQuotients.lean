/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flat quotients after restricting scalars from a completion

If a ring map `f : A^∧ → S` from the `I`-adic completion of `A` is flat when restricted to `A`,
then `S` is flat modulo every power of the extended ideal `J = I A^∧`.

## Implementation details

Finite generation of `I` identifies `A^∧ ⧸ J^n` with `A ⧸ I^n`, and `I^n S = J^n S`. Flatness
of `S ⧸ I^n S` over `A ⧸ I^n` follows by flat base change and is transported along this
isomorphism.

## References

* [Stacks, Tag 0C4G], forward implication, quotient comparison in the second paragraph
* [Stacks, Tag 05GG] (completion modulo powers)
* [Stacks, Tag 00HI] (flat base change)
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- Flatness after restriction to the original ring gives flatness modulo powers
of the extended ideal. -/
theorem flat_quotients_of_flat_restriction
    {A : Type u} {S : Type v} [CommRing A] [CommRing S]
    (I : Ideal A) (hI : I.FG) (f : AdicCompletion I A →+* S)
    (hflat : (f.comp (algebraMap A (AdicCompletion I A))).Flat) :
    letI : Algebra (AdicCompletion I A) S := f.toAlgebra
    ∀ n : ℕ,
      Module.Flat
        (AdicCompletion I A ⧸ (I.map (algebraMap A (AdicCompletion I A))) ^ n)
        (S ⧸ ((I.map (algebraMap A (AdicCompletion I A))) ^ n) •
          (⊤ : Submodule (AdicCompletion I A) S)) := by
  let C := AdicCompletion I A
  let ι : A →+* C := algebraMap A C
  let J := I.map ι
  let g : A →+* S := f.comp ι
  let : Algebra C S := f.toAlgebra
  let : Algebra A S := g.toAlgebra
  have : IsScalarTower A C S := .of_algebraMap_eq fun _ ↦ rfl
  change ∀ n : ℕ, Module.Flat (C ⧸ J ^ n) (S ⧸ (J ^ n) • (⊤ : Submodule C S))
  intro n
  have hker : RingHom.ker (AdicCompletion.evalₐ I n).toRingHom = J ^ n := by
    ext x
    rw [RingHom.mem_ker]
    rw [← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change (AdicCompletion.evalₐ I n) x = 0 ↔ AdicCompletion.eval I A n x = 0
    let e₀ := Ideal.quotientEquivAlgOfEq A
      (show (I ^ n • ⊤ : Ideal A) = I ^ n by simp)
    change e₀ (AdicCompletion.eval I A n x) = 0 ↔ AdicCompletion.eval I A n x = 0
    exact map_eq_zero_iff e₀ e₀.injective
  let e : C ⧸ J ^ n ≃+* A ⧸ I ^ n :=
    (Ideal.quotEquivOfEq hker.symm).trans
      ((AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
        (AdicCompletion.surjective_evalₐ I n))
  have he (a : A) : e (Ideal.Quotient.mk (J ^ n) (ι a)) =
      Ideal.Quotient.mk (I ^ n) a := by
    change (AdicCompletion.evalₐ I n).toRingHom.quotientKerEquivOfSurjective
      (AdicCompletion.surjective_evalₐ I n) (Ideal.Quotient.mk _ (ι a)) = _
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    exact AdicCompletion.evalₐ_of I n a
  let K := (I ^ n).map g
  have hJK : (J ^ n).map f = K := by
    simp [J, K, g, ← Ideal.map_pow, Ideal.map_map]
  let qf : C ⧸ J ^ n →+* S ⧸ K :=
    Ideal.quotientMap K f (Ideal.map_le_iff_le_comap.mp (le_of_eq hJK))
  let : Algebra (A ⧸ I ^ n) (S ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.le_comap_map : I ^ n ≤ K.comap (algebraMap A S))
  have hflatQ : (algebraMap (A ⧸ I ^ n) (S ⧸ K)).Flat := by
    have : Module.Flat A S := hflat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (I ^ n)).toLinearEquiv
  have hqf : qf.Flat := by
    apply (RingHom.Flat.comp_iff_of_bijective_right
      (f := qf) (g := e.symm.toRingHom) e.symm.bijective).mp
    have hcomp : qf.comp e.symm.toRingHom = algebraMap (A ⧸ I ^ n) (S ⧸ K) := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change qf (e.symm (Ideal.Quotient.mk (I ^ n) a)) =
        Ideal.Quotient.mk K (g a)
      have hpre := congrArg e.symm (he a)
      rw [e.symm_apply_apply] at hpre
      rw [← hpre]
      rfl
    rw [hcomp]
    exact hflatQ
  let : Algebra (C ⧸ J ^ n) (S ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (le_of_eq hJK))
  have : Module.Flat (C ⧸ J ^ n) (S ⧸ K) :=
    RingHom.flat_algebraMap_iff.mp hqf
  let eQ : (S ⧸ (J ^ n) • (⊤ : Submodule C S)) ≃ₗ[C] S ⧸ K :=
    (Submodule.quotEquivOfEq _ _ (by
      rw [Ideal.smul_top_eq_map, f.algebraMap_toAlgebra, hJK])).trans
      (Submodule.Quotient.restrictScalarsEquiv C K)
  have eQlinear : ∀ (r : C ⧸ J ^ n) x, eQ (r • x) = r • eQ x := by
    intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact Module.Flat.of_linearEquiv (eQ.toAddEquiv.toLinearEquiv eQlinear)

end AdicCompletion
