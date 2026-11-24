/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.CompletionRestrictionFlatQuotients
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.Flat.FlatModulePowers

/-!
# Flatness of completion along a flat local map

A flat local homomorphism of Noetherian local rings induces a flat homomorphism of their
adic completions.

## Main results

* `flat_adicCompletion_of_flat_local`

## References

* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)
-/

@[expose] public section

universe u v

/-- A flat local homomorphism `φ : A → B` of Noetherian local rings induces a flat
homomorphism `φhat` of adic completions, characterized levelwise by the induced maps
`A / mA ^ n → B / mB ^ n` and compatible with the canonical maps to the completions. -/
theorem flat_adicCompletion_of_flat_local
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (hlocal : ∀ x : A, x ∈ IsLocalRing.maximalIdeal A →
      φ x ∈ IsLocalRing.maximalIdeal B) :
    let mA : Ideal A := IsLocalRing.maximalIdeal A
    let mB : Ideal B := IsLocalRing.maximalIdeal B
    let Ahat := AdicCompletion mA A
    let Bhat := AdicCompletion mB B
    let ιA : A →+* Ahat := algebraMap A Ahat
    let ιB : B →+* Bhat := algebraMap B Bhat
    ∃ φhat : Ahat →+* Bhat,
      (∀ n : ℕ,
        ((AdicCompletion.evalₐ mB n).toRingHom).comp φhat =
          (Ideal.Quotient.lift (mA ^ n)
            ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
              intro x hx
              change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
              rw [Ideal.Quotient.eq_zero_iff_mem]
              exact (pow_le_pow_left' ((Ideal.map_le_iff_le_comap).2 (by
                intro y hy
                exact hlocal y hy)) n) (by
                  rw [← Ideal.map_pow]
                  exact Ideal.mem_map_of_mem φ hx)) ).comp
            (AdicCompletion.evalₐ mA n).toRingHom) ∧
      φhat.comp ιA = ιB.comp φ ∧ φhat.Flat := by
  dsimp only
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  have hmap : mA.map φ ≤ mB := Ideal.map_le_iff_le_comap.mpr hlocal
  have hpow (n : ℕ) : (mA ^ n).map φ ≤ mB ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  let qmap (n : ℕ) : A ⧸ mA ^ n →+* B ⧸ mB ^ n :=
    Ideal.Quotient.lift (mA ^ n) ((Ideal.Quotient.mk (mB ^ n)).comp φ) (by
      intro x hx
      change Ideal.Quotient.mk (mB ^ n) (φ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hpow n (Ideal.mem_map_of_mem φ hx))
  let f (n : ℕ) := (qmap n).comp (AdicCompletion.evalₐ mA n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow mB hmn).comp (f n) = f m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [f, qmap] using congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk mA hmn x)
  let φhat := AdicCompletion.liftRingHom mB f (fun hmn ↦ hf hmn)
  have heval (n : ℕ) : (AdicCompletion.evalₐ mB n).toRingHom.comp φhat = f n :=
    AdicCompletion.evalₐ_comp_liftRingHom mB f (fun hmn ↦ hf hmn) n
  have hcomp : φhat.comp (algebraMap A (AdicCompletion mA A)) =
      (algebraMap B (AdicCompletion mB B)).comp φ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    simpa [f, qmap, AdicCompletion.algebraMap_apply] using
      RingHom.congr_fun (heval n) ((algebraMap A (AdicCompletion mA A)) x)
  refine ⟨φhat, heval, hcomp, ?_⟩
  let : Algebra (AdicCompletion mA A) (AdicCompletion mB B) := φhat.toAlgebra
  let := AdicCompletion.isNoetherianRing mA
  let := AdicCompletion.isNoetherianRing mB
  have hflatB : (algebraMap B (AdicCompletion mB B)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hflatA : (φhat.comp (algebraMap A (AdicCompletion mA A))).Flat := by
    rw [hcomp]
    exact hφ.comp hflatB
  have hquot := AdicCompletion.flat_quotients_of_flat_restriction mA
    (IsNoetherian.noetherian mA) φhat hflatA
  have hmax : (mA.map (algebraMap A (AdicCompletion mA A))).map
      (algebraMap (AdicCompletion mA A) (AdicCompletion mB B)) ≤
      IsLocalRing.maximalIdeal (AdicCompletion mB B) := by
    rw [Ideal.map_map, φhat.algebraMap_toAlgebra, hcomp,
      ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_mono hmap
  change Module.Flat (AdicCompletion mA A) (AdicCompletion mB B)
  exact (Module.Flat.flat_of_flat_quotients_powers
    (M := AdicCompletion mB B) (mA.map (algebraMap A (AdicCompletion mA A)))
    (fun n _ ↦ hquot n)).2 hmax
