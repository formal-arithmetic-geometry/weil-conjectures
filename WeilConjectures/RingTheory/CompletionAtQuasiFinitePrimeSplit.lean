/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.Ring
import WeilConjectures.RingTheory.FiniteCompletionFactorIdempotent

/-!
# A completion factor from a finite subalgebra agreeing away from an element

If a finite subalgebra `S'` of `S` agrees with `S` after inverting some `g ∉ q`, then the
completion of `S_q` is a direct factor of `R_p^∧ ⊗[R] S`.

## Implementation details

The idempotent `e` and the element `v` with `v γ = e` (where `γ = 1 ⊗ g`) come from the finite
tensor product `R_p^∧ ⊗[R] S'`. Surjectivity of the away map lets one clear a common power of
`γ` from every element of `R_p^∧ ⊗[R] S`, which is enough to transfer the kernel comparison;
no tensor-localization theorem is needed. The complementary factor `B` is the corner of
`1 - δ`, where `δ` is the image of `e`.

## References

* [Stacks, Tag 07NC], the proof after the choice of the finite subalgebra
-/

@[expose] public section

universe u v

namespace Algebra


/-- Clear a common power of the away parameter from an arbitrary tensor. -/
private theorem tensor_clear_away
    {R : Type u} {S : Type v} {A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (S' : Subalgebra R S) (g : S')
    (haway : Function.Surjective (Localization.awayMap S'.val.toRingHom g)) :
    let j := (TensorProduct.map (AlgHom.id R A) S'.val).toRingHom
    let γ := TensorProduct.tmul R (1 : A) g
    ∀ u : TensorProduct R A S, ∃ t n, j t = (j γ) ^ n * u := by
  dsimp only
  let j := (TensorProduct.map (AlgHom.id R A) S'.val).toRingHom
  let γ := TensorProduct.tmul R (1 : A) g
  have hs := Localization.awayMap_surjective_iff.mp haway
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨z, n, hz⟩ := hs y
    change z.1 = g.1 ^ n * y at hz
    refine ⟨TensorProduct.tmul R x z, n, ?_⟩
    change TensorProduct.tmul R x z.1 =
      (TensorProduct.tmul R (1 : A) g.1) ^ n * TensorProduct.tmul R x y
    rw [TensorProduct.tmul_pow, TensorProduct.tmul_mul_tmul]
    simpa only [one_pow, one_mul] using congrArg (fun z : S ↦ TensorProduct.tmul R x z) hz
  | add x y hx hy =>
    obtain ⟨tx, n, hn⟩ := hx
    obtain ⟨ty, m, hm⟩ := hy
    refine ⟨γ ^ m * tx + γ ^ n * ty, n + m, ?_⟩
    change j (γ ^ m * tx + γ ^ n * ty) = (j γ) ^ (n + m) * (x + y)
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hn, hm, pow_add]
    ring

/-- Transport a surjective factor map through a map with clearable denominators. -/
private theorem split_factor_of_clear_denominators
    {T : Type u} {U : Type v} {C : Type*} [CommRing T] [CommRing U] [CommRing C]
    (j : T →+* U) (φ : U →+* C) (γ e v : T)
    (he : IsIdempotentElem e) (hve : v * γ = e)
    (hφe : φ (j e) = 1)
    (hs : Function.Surjective (φ.comp j))
    (hk : ∀ t, φ (j t) = 0 → e * t = 0)
    (hclear : ∀ u : U, ∃ t n, j t = (j γ) ^ n * u) :
    ∃ (B : Type v) (_ : CommRing B) (β : U →+* B),
      ∃ E : U ≃+* C × B, E.toRingHom = RingHom.prod φ β := by
  let δ := j e
  have hδ : IsIdempotentElem δ := he.map j
  have hφδ : φ δ = 1 := hφe
  have hpow (n : ℕ) : δ * (j v) ^ n * (j γ) ^ n = δ := by
    rw [mul_assoc, ← mul_pow, ← map_mul, hve]
    cases n with
    | zero => simp
    | succ n => rw [hδ.pow_succ_eq, hδ.eq]
  have H (x y : U) : φ x = φ y ↔ δ * x = δ * y := by
    constructor
    · intro hxy
      obtain ⟨t, n, ht⟩ := hclear (x - y)
      have ht0 : φ (j t) = 0 := by rw [ht, map_mul, map_sub, hxy, sub_self, mul_zero]
      have het := congrArg j (hk t ht0)
      have hzero : δ * (x - y) = 0 := by
        calc
          δ * (x - y) = (δ * (j v) ^ n * (j γ) ^ n) * (x - y) := by rw [hpow]
          _ = (j v) ^ n * (δ * j t) := by rw [ht]; ring
          _ = 0 := by
            have hz : δ * j t = 0 := by simpa only [map_mul, map_zero] using het
            rw [hz, mul_zero]
      exact sub_eq_zero.mp (by simpa [mul_sub] using hzero)
    · intro hxy
      simpa only [map_mul, hφδ, one_mul] using congrArg φ hxy
  let β : U →+* hδ.one_sub.Corner :=
    { toFun := fun x ↦ ⟨(1 - δ) * x, (Subsemigroup.mem_corner_iff hδ.one_sub).mpr
        ⟨by rw [← mul_assoc, hδ.one_sub.eq],
          by rw [mul_assoc, mul_comm x (1 - δ), ← mul_assoc, hδ.one_sub.eq]⟩⟩
      map_one' := by apply Subtype.ext; exact mul_one (1 - δ)
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        change (1 - δ) * (x * y) = ((1 - δ) * x) * ((1 - δ) * y)
        calc
          _ = ((1 - δ) * (1 - δ)) * (x * y) := by rw [hδ.one_sub.eq]
          _ = _ := by ring
      map_zero' := by apply Subtype.ext; exact mul_zero (1 - δ)
      map_add' := fun x y ↦ by apply Subtype.ext; exact mul_add (1 - δ) x y }
  have hbij : Function.Bijective (RingHom.prod φ β) := by
    constructor
    · intro x y hxy
      have hδxy := (H x y).mp (congrArg Prod.fst hxy)
      have hβxy := congrArg (fun z : C × hδ.one_sub.Corner ↦ z.2.1) hxy
      change (1 - δ) * x = (1 - δ) * y at hβxy
      calc
        x = δ * x + (1 - δ) * x := by ring
        _ = δ * y + (1 - δ) * y := by rw [hδxy, hβxy]
        _ = y := by ring
    · rintro ⟨c, y⟩
      obtain ⟨t, ht⟩ := hs c
      have hfy : (1 - δ) * y.1 = y.1 :=
        ((Subsemigroup.mem_corner_iff hδ.one_sub).mp y.2).1
      have hφy : φ y.1 = 0 := by
        rw [← hfy, map_mul, map_sub, map_one, hφδ, sub_self, zero_mul]
      refine ⟨δ * j t + y.1, ?_⟩
      apply Prod.ext
      · change φ (δ * j t + y.1) = c
        simpa [hφδ, hφy] using ht
      · apply Subtype.ext
        change (1 - δ) * (δ * j t + y.1) = y.1
        rw [mul_add, ← mul_assoc, sub_mul, one_mul, hδ.eq, sub_self, zero_mul,
          zero_add, hfy]
  exact ⟨hδ.one_sub.Corner, inferInstance, β,
    RingEquiv.ofBijective (RingHom.prod φ β) hbij, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- A finite subalgebra agreeing with `S` away from an element `g ∉ q` gives a direct
completion factor: for any map `ψ` of completions compatible with the local map, the natural
map `φ : R_p^∧ ⊗[R] S → S_q^∧` is the first component of an isomorphism with `S_q^∧ × B`. -/
theorem completion_split_of_finite_subalgebra_away
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (q : PrimeSpectrum S)
    (S' : Subalgebra R S) [Module.Finite R S']
    (g : S') (hg : g.1 ∉ q.asIdeal)
    (haway : Function.Bijective (Localization.awayMap S'.val.toRingHom g)) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let U := TensorProduct R Rph S
    ∀ (ψ : Rph →+* Sqh),
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) →
      ∃ (B : Type (max u v)) (_ : CommRing B) (β : U →+* B) (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S),
          φ (TensorProduct.tmul R x y) =
            ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) ∧
        ∃ e : U ≃+* Sqh × B, e.toRingHom = RingHom.prod φ β := by
  intro p Rp Sq Ip Iq Rph Sqh f U ψ hψ
  classical
  let T := TensorProduct R Rph S'
  have hψR (r : R) : ψ (algebraMap R Rph r) = algebraMap R Sqh r := by
    apply AdicCompletion.ext_evalₐ
    intro n
    have h := hψ n (algebraMap R Rph r) (algebraMap R Rp r) (by
      change AdicCompletion.evalₐ Ip n
        (AdicCompletion.of Ip Rp (algebraMap R Rp r)) = _
      exact AdicCompletion.evalₐ_of Ip n _)
    change AdicCompletion.evalₐ Iq n (ψ (algebraMap R Rph r)) = _ at h ⊢
    rw [show algebraMap R Sqh r = AdicCompletion.of Iq Sq (algebraMap R Sq r)
      from rfl, AdicCompletion.evalₐ_of]
    change AdicCompletion.evalₐ Iq n (ψ (algebraMap R Rph r)) =
      Ideal.Quotient.mk (Iq ^ n)
        (Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
          (algebraMap R (Localization.AtPrime p) r)) at h
    rw [Localization.localRingHom_to_map] at h
    exact h
  let ψₐ : Rph →ₐ[R] Sqh := { ψ with commutes' := hψR }
  let ι : S →ₐ[R] Sqh := IsScalarTower.toAlgHom R S Sqh
  let φ : U →+* Sqh :=
    (TensorProduct.lift ψₐ ι (fun _ _ ↦ Commute.all _ _)).toRingHom
  have hφ (x : Rph) (y : S) : φ (TensorProduct.tmul R x y) =
      ψ x * algebraMap Sq Sqh (algebraMap S Sq y) := by
    change ψ x * algebraMap S Sqh y = _
    rw [IsScalarTower.algebraMap_apply S Sq Sqh]
  let j : T →+* U := (TensorProduct.map (AlgHom.id R Rph) S'.val).toRingHom
  let γ : T := TensorProduct.tmul R (1 : Rph) g
  obtain ⟨e, v, he, hve, hφe, hs, hk⟩ :=
    finite_completion_factor_idempotent R S q S' g hg haway ψ hψ φ hφ
  obtain ⟨B, hB, β, F, hF⟩ := split_factor_of_clear_denominators
    j φ γ e v he hve hφe hs hk (tensor_clear_away S' g haway.2)
  exact ⟨B, hB, β, φ, hφ, F, hF⟩

end Algebra
