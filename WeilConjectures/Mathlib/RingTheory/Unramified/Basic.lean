/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.Basic

/-!
# Sections of unramified algebras

If `A` is a formally unramified `P`-algebra and `σ : A ⟶ C` has a section `f`, then the kernel of
`σ` is idempotent modulo any ideal `J` modulo which `σ` is `P`-linear.

## Main statements

- `Algebra.FormallyUnramified.ker_le_sup_ker_sq_of_section`
-/

@[expose] public section

namespace Algebra.FormallyUnramified

/-- Let `A` be formally unramified over `P`, let `σ : A ⟶ C` and `f : C ⟶ A` with
`σ ∘ f = id`, and let `J` be an ideal such that `σ` is a `P`-algebra map modulo `J`, that is
`a - f(σ(a)) ∈ J` for `a` in the image of `P`. Then `ker σ ⊆ J + (ker σ)²`. -/
lemma ker_le_sup_ker_sq_of_section {P A C : Type*} [CommRing P] [CommRing A] [CommRing C]
    [Algebra P A] [FormallyUnramified P A] (σ : A →+* C) (f : C →+* A)
    (hσf : σ.comp f = RingHom.id C) (J : Ideal A)
    (hP : ∀ p : P, algebraMap P A p - f (σ (algebraMap P A p)) ∈ J) :
    RingHom.ker σ ≤ J ⊔ RingHom.ker σ ^ 2 := by
  set K := RingHom.ker σ
  set N : Ideal (A ⧸ (J ⊔ K ^ 2)) := K.map (Ideal.Quotient.mk _)
  have hN : N ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hx))
  have hσf' : ∀ c, σ (f c) = c := fun c ↦ congr($hσf c)
  let g₂ : A →ₐ[P] A ⧸ (J ⊔ K ^ 2) :=
    { (Ideal.Quotient.mk _).comp (f.comp σ) with
      commutes' p := by
        change Ideal.Quotient.mk _ (f (σ (algebraMap P A p))) =
          Ideal.Quotient.mk _ (algebraMap P A p)
        rw [Ideal.Quotient.eq]
        exact Ideal.mem_sup_left (by simpa using J.neg_mem (hP p)) }
  have key := FormallyUnramified.comp_injective (R := P) (A := A) N hN
    (a₁ := Ideal.Quotient.mkₐ P (J ⊔ K ^ 2)) (a₂ := g₂) (by
      ext x
      change Ideal.Quotient.mk N (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk N (Ideal.Quotient.mk _ (f (σ x)))
      rw [Ideal.Quotient.eq, ← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, hσf', sub_self])
  intro x hx
  have := congr($key x)
  change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ (f (σ x)) at this
  rw [RingHom.mem_ker.mp hx, map_zero, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end Algebra.FormallyUnramified
