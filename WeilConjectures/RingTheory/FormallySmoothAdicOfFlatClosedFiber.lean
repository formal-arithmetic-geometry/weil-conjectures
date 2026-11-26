/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicClosedFiberCompletion
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete

/-!
# Adic formal smoothness from flatness and the closed fibre

A flat local homomorphism of Noetherian local rings whose closed fibre is formally smooth for
its maximal-ideal-adic topology is formally smooth for the maximal-ideal-adic topology.

## Implementation details

We pass to maximal-ideal completions: the completed map is flat, its closed fibre is the
completion of the original closed fibre and so is again formally smooth (Tag 07ED). The
complete case is `RingHom.formallySmoothAdic_of_flat_closedFiber_complete`, which uses a Cohen
presentation (Tag 07NN) and power-series coordinates (Tags 07NL, 07NM). Finally a lifting
problem for `A → B` killing `m_B ^ n` factors through the completions, using
`A ⧸ m_A ^ (2 * n) ≃ Â ⧸ (m_A Â) ^ (2 * n)`, and the lift over the completions restricts to
`B`.

## References

* [Stacks, Tag 07NQ], (2) implies (3)
* [Stacks, Tag 07ED]
* [Stacks, Tag 07NL]
* [Stacks, Tag 07NM]
* [Stacks, Tag 07NN]
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom

private theorem completion_eval_ker
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom =
      maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
  ext x
  rw [AdicCompletion.maximalIdeal_eq_map, RingHom.mem_ker, ← Ideal.map_pow]
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian (maximalIdeal R))]
  change AdicCompletion.evalₐ (maximalIdeal R) n x = 0 ↔
    AdicCompletion.eval (maximalIdeal R) R n x = 0
  let e := Ideal.quotientEquivAlgOfEq R
    (show ((maximalIdeal R) ^ n • ⊤ : Ideal R) = (maximalIdeal R) ^ n by simp)
  exact map_eq_zero_iff e e.injective

/-- If the induced map of maximal-ideal completions is formally smooth for the
maximal-ideal-adic topology, then so is the original local map. -/
private theorem formallySmoothAdic_of_completion
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f]
    (ψ : AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B)
    [IsLocalHom ψ]
    (hcomm : ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp f)
    (hfs : letI := ψ.toAlgebra
      Algebra.FormallySmoothAdic (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B)
        (maximalIdeal (AdicCompletion (maximalIdeal B) B))) :
    let := f.toAlgebra
    Algebra.FormallySmoothAdic A B (maximalIdeal B) := by
  dsimp only
  let := f.toAlgebra
  intro D _ _ J hJ g hg
  obtain ⟨k, hk, hgk⟩ := hg
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Bhat := AdicCompletion (maximalIdeal B) B
  let cA : A →+* Ahat := algebraMap A Ahat
  let cB : B →+* Bhat := algebraMap B Bhat
  have hcomm' (a : A) : ψ (cA a) = cB (f a) := RingHom.congr_fun hcomm a
  let α : A →+* D := algebraMap A D
  have hαJ : (maximalIdeal A) ^ k ≤ J.comap α := by
    intro a ha
    change α a ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hfa : f a ∈ (maximalIdeal B) ^ k := by
      exact (pow_le_pow_left' (map_maximalIdeal_le f) k)
        (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f ha)
    exact (g.commutes a).symm.trans (hgk (f a) hfa)
  have hαkill : ∀ a ∈ (maximalIdeal A) ^ (k + k), α a = 0 := by
    have hp : (maximalIdeal A) ^ (k + k) ≤ (J ^ 2).comap α := by
      rw [pow_add, pow_two]
      exact (Ideal.mul_mono hαJ hαJ).trans (Ideal.le_comap_mul _)
    rw [hJ] at hp
    exact fun a ha ↦ hp ha
  let αhat : Ahat →+* D :=
    (Ideal.Quotient.lift ((maximalIdeal A) ^ (k + k)) α hαkill).comp
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k)).toRingHom
  have hαhat (a : A) : αhat (cA a) = α a := by
    change Ideal.Quotient.lift _ α hαkill
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a)) = α a
    rw [show AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a) =
      Ideal.Quotient.mk ((maximalIdeal A) ^ (k + k)) a from
        AdicCompletion.evalₐ_of _ _ a]
    rfl
  let ghat : Bhat →+* D ⧸ J :=
    (Ideal.Quotient.lift ((maximalIdeal B) ^ k) g.toRingHom hgk).comp
      (AdicCompletion.evalₐ (maximalIdeal B) k).toRingHom
  have hghat (b : B) : ghat (cB b) = g b := by
    change Ideal.Quotient.lift _ g.toRingHom hgk
      (AdicCompletion.evalₐ (maximalIdeal B) k (cB b)) = g b
    rw [show AdicCompletion.evalₐ (maximalIdeal B) k (cB b) =
      Ideal.Quotient.mk ((maximalIdeal B) ^ k) b from AdicCompletion.evalₐ_of _ _ b]
    rfl
  have hghatkill : ∀ b ∈ maximalIdeal Bhat ^ k, ghat b = 0 := by
    intro b hb
    rw [← completion_eval_ker B k] at hb
    change Ideal.Quotient.lift _ g.toRingHom hgk
      (AdicCompletion.evalₐ (maximalIdeal B) k b) = 0
    rw [show AdicCompletion.evalₐ (maximalIdeal B) k b = 0 from hb, map_zero]
  let : Algebra Ahat Bhat := ψ.toAlgebra
  let : Algebra Ahat D := αhat.toAlgebra
  let ghatA : Bhat →ₐ[Ahat] D ⧸ J := ⟨ghat, by
    intro a
    obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) (k + k) a)
    have hd : a - cA a₀ ∈ maximalIdeal Ahat ^ (k + k) := by
      rw [← completion_eval_ker A (k + k), RingHom.mem_ker]
      change AdicCompletion.evalₐ (maximalIdeal A) (k + k) (a - cA a₀) = 0
      rw [map_sub, show AdicCompletion.evalₐ (maximalIdeal A) (k + k) (cA a₀) =
        Ideal.Quotient.mk ((maximalIdeal A) ^ (k + k)) a₀ from
          AdicCompletion.evalₐ_of _ _ a₀, ha₀, sub_self]
    have hψd : ψ (a - cA a₀) ∈ maximalIdeal Bhat ^ k := by
      apply Ideal.pow_le_pow_right (Nat.le_add_right k k)
      exact (pow_le_pow_left' (map_maximalIdeal_le ψ) (k + k))
        (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ψ hd)
    have hgd : ghat (ψ a) = ghat (ψ (cA a₀)) := by
      simpa only [map_sub, sub_eq_zero] using hghatkill _ hψd
    have hαa : αhat a = α a₀ := by
      change Ideal.Quotient.lift _ α hαkill
        (AdicCompletion.evalₐ (maximalIdeal A) (k + k) a) = α a₀
      rw [← ha₀]
      rfl
    change ghat (ψ a) = Ideal.Quotient.mk J (αhat a)
    rw [hgd, hcomm' a₀, hghat, hαa]
    exact g.commutes a₀⟩
  obtain ⟨l, hl⟩ := hfs J hJ ghatA ⟨k, hk, hghatkill⟩
  let lB : B →ₐ[A] D := ⟨l.toRingHom.comp cB, by
    intro a
    change l (cB (f a)) = α a
    rw [← hcomm' a]
    exact (l.commutes (cA a)).trans (hαhat a)⟩
  refine ⟨lB, ?_⟩
  ext b
  exact (AlgHom.congr_fun hl (cB b)).trans (hghat b)

/-- A flat local map of Noetherian local rings with adically formally smooth closed fibre
is formally smooth for the maximal-ideal-adic topology on the target.
The residue field and closed fibre are the canonical quotients, with the induced quotient
algebra structure. The image of `maximalIdeal B` in the closed fibre is its maximal ideal. -/
theorem formallySmoothAdic_of_flat_closedFiber
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
      Algebra.FormallySmoothAdic A B (maximalIdeal B) := by
  dsimp only
  let : Algebra A B := f.toAlgebra
  intro hfibre
  let Ahat := AdicCompletion (maximalIdeal A) A
  let Bhat := AdicCompletion (maximalIdeal B) B
  have : IsNoetherianRing Ahat := AdicCompletion.isNoetherianRing _
  have : IsNoetherianRing Bhat := AdicCompletion.isNoetherianRing _
  obtain ⟨ψ, _, hcomm, hψflat⟩ := flat_adicCompletion_of_flat_local A B f hflat
    (fun x hx ↦ map_maximalIdeal_le f (Ideal.mem_map_of_mem f hx))
  have : IsLocalHom ψ := by
    apply ((local_hom_TFAE ψ).out 1 3).mpr
    rw [AdicCompletion.maximalIdeal_eq_map (R := A), Ideal.map_map, hcomm,
      ← Ideal.map_map, AdicCompletion.maximalIdeal_eq_map (R := B)]
    exact Ideal.map_mono (map_maximalIdeal_le f)
  have hclosed := formallySmoothAdic_closedFiber_completion A B f ψ hcomm hfibre
  have hcomplete := formallySmoothAdic_of_flat_closedFiber_complete Ahat Bhat ψ
    hψflat hclosed
  exact formallySmoothAdic_of_completion A B f ψ hcomm hcomplete

end RingHom
