/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Rings that lift idempotents

A commutative ring `A` *lifts idempotents* if every idempotent of every quotient of `A` is the
image of an idempotent of `A` (`Ring.LiftsIdempotents`).

## Main results

* `Ring.liftsIdempotents_of_isLocalRing`: local rings lift idempotents;
* `Ring.LiftsIdempotents.prod`: a product of two rings that lift idempotents lifts idempotents;
* `Ring.LiftsIdempotents.of_isCoprime`: if `A` has two coprime ideals with trivial intersection
  whose quotients lift idempotents, then so does `A`.
-/

@[expose] public section

/-- An idempotent unit is `1`. -/
theorem IsIdempotentElem.eq_one_of_isUnit {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have hz : (u : S) * (u - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  linear_combination (u.isUnit.mul_right_eq_zero).mp hz

namespace Ring

/-- A commutative ring `A` *lifts idempotents* if for every ideal `I` of `A`, every idempotent
of `A ⧸ I` is the image of an idempotent of `A`. -/
def LiftsIdempotents (A : Type*) [CommRing A] : Prop :=
  ∀ (I : Ideal A) (x : A), x * x - x ∈ I → ∃ e : A, IsIdempotentElem e ∧ e - x ∈ I

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The zero ring lifts idempotents. -/
theorem liftsIdempotents_of_subsingleton [Subsingleton A] : LiftsIdempotents A :=
  fun _ x _ ↦ ⟨x, Subsingleton.elim _ _, by simp⟩

/-- A local ring lifts idempotents, since it has no nontrivial idempotents at all. -/
theorem liftsIdempotents_of_isLocalRing [IsLocalRing A] : LiftsIdempotents A := by
  intro I x hx
  have hx' : x * (x - 1) ∈ I := by rw [mul_sub, mul_one]; exact hx
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with h | h
  · refine ⟨1, IsIdempotentElem.one, ?_⟩
    rw [show (1 : A) - x = -(x - 1) by ring]
    exact I.neg_mem ((I.unit_mul_mem_iff_mem h).mp hx')
  · refine ⟨0, IsIdempotentElem.zero, ?_⟩
    rw [zero_sub]
    refine I.neg_mem ((I.unit_mul_mem_iff_mem h).mp ?_)
    rw [show (1 - x) * x = -(x * (x - 1)) by ring]
    exact I.neg_mem hx'

/-- Lifting idempotents transfers along a ring isomorphism. -/
theorem LiftsIdempotents.of_ringEquiv (e : A ≃+* B) (h : LiftsIdempotents A) :
    LiftsIdempotents B := by
  intro I x hx
  obtain ⟨f, hf, hfx⟩ := h (I.comap (e : A →+* B)) (e.symm x) (by simpa using hx)
  refine ⟨e f, hf.map (e : A →+* B), ?_⟩
  rw [Ideal.mem_comap] at hfx
  simpa using hfx

/-- A product of two rings lifting idempotents lifts idempotents. -/
theorem LiftsIdempotents.prod (hA : LiftsIdempotents A) (hB : LiftsIdempotents B) :
    LiftsIdempotents (A × B) := by
  intro I x hx
  rw [Ideal.ideal_prod_eq I, Ideal.mem_prod] at hx
  obtain ⟨e₁, h₁, h₁'⟩ := hA _ x.1 hx.1
  obtain ⟨e₂, h₂, h₂'⟩ := hB _ x.2 hx.2
  refine ⟨(e₁, e₂), Prod.ext h₁ h₂, ?_⟩
  rw [Ideal.ideal_prod_eq I, Ideal.mem_prod]
  exact ⟨h₁', h₂'⟩

/-- If two coprime ideals of `A` intersect in `0` and both quotients lift idempotents, then
so does `A`. -/
theorem LiftsIdempotents.of_isCoprime {J₁ J₂ : Ideal A} (hcop : IsCoprime J₁ J₂)
    (hbot : J₁ ⊓ J₂ = ⊥) (h₁ : LiftsIdempotents (A ⧸ J₁)) (h₂ : LiftsIdempotents (A ⧸ J₂)) :
    LiftsIdempotents A :=
  (h₁.prod h₂).of_ringEquiv
    (((RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq hbot.symm)).trans
      (Ideal.quotientInfEquivQuotientProd J₁ J₂ hcop)).symm

end Ring
