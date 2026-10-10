/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Topology.LocallyConstant.Algebra

/-!

# The ring of locally constant functions on a compact space

Let `X` be a compact topological space and `R` a commutative ring. This file records algebraic
properties of the ring `LocallyConstant X R` of locally constant functions `X → R` with the
pointwise operations, used to show that `Spec (LocallyConstant X ℤ) = X × Spec ℤ` is weakly
étale over `Spec ℤ` and that a surjection of profinite sets induces a surjection of spectra.

* The characteristic function of a clopen subset is an idempotent
  (`LocallyConstant.isIdempotentElem_charFn`), and `LocallyConstant X ℤ` is generated as a ring
  by these idempotents (`LocallyConstant.subring_closure_isIdempotentElem_eq_top`): a locally
  constant function on a compact space takes finitely many values `v`, and is the sum of the
  `v • 1_{f⁻¹(v)}`.
* Every prime ideal `p` of `LocallyConstant X R` lies over a point `x ∈ X`, in the sense that it
  contains the kernel of the evaluation at `x` (`LocallyConstant.exists_ker_evalRingHom_le`).
  Otherwise, for every `x` there is `f_x ∉ p` with `f_x(x) = 0`; the clopens `f_x⁻¹(0)` cover
  `X`, finitely many `x₁, …, xₙ` suffice by compactness, the idempotents `e_i = 1_{f_{xᵢ}⁻¹(0)}`
  lie in `p` because `f_{xᵢ} e_i = 0`, and `∏ (1 - e_i) = 0` gives `1 ∈ p`.
* Consequently a prime ideal `p` lying over `x = π(y)`, for a continuous map `π : Y → X`, is the
  preimage of a prime ideal of `LocallyConstant Y R` under `π^*`
  (`LocallyConstant.exists_isPrime_comap_comapRingHom_eq`), namely of `ev_y⁻¹(ev_x(p))`.

-/

@[expose] public section

namespace LocallyConstant

variable {X : Type*} [TopologicalSpace X]

/-- The characteristic function of a clopen subset is an idempotent. -/
lemma isIdempotentElem_charFn (Y : Type*) [MulZeroOneClass Y] {U : Set X} (hU : IsClopen U) :
    IsIdempotentElem (charFn Y hU) := by
  change charFn Y hU * charFn Y hU = charFn Y hU
  ext x
  by_cases hx : x ∈ U <;> simp [coe_charFn, hx]

section Compact

lemma intCast_apply (v : ℤ) (x : X) : (v : LocallyConstant X ℤ) x = v :=
  rfl

variable [CompactSpace X]

/-- A locally constant integer-valued function `f` on a compact space is the finite sum over its
values `v` of `v • 1_{f⁻¹(v)}`. -/
lemma eq_sum_intCast_mul_charFn (f : LocallyConstant X ℤ) :
    f = ∑ v ∈ f.range_finite.toFinset,
      (v : LocallyConstant X ℤ) * charFn ℤ (f.isLocallyConstant.isClopen_fiber v) := by
  ext x
  rw [show (⇑(∑ v ∈ f.range_finite.toFinset,
      (v : LocallyConstant X ℤ) * charFn ℤ (f.isLocallyConstant.isClopen_fiber v)) : X → ℤ) =
      ∑ v ∈ f.range_finite.toFinset,
        ⇑((v : LocallyConstant X ℤ) * charFn ℤ (f.isLocallyConstant.isClopen_fiber v)) from
      map_sum coeFnAddMonoidHom _ _, Finset.sum_apply,
    Finset.sum_eq_single (f x) (fun v _ hv ↦ ?_) (fun h ↦ (h (by simp)).elim)]
  · simp [coe_charFn, intCast_apply]
  · simp [coe_charFn, intCast_apply, Ne.symm hv]

/-- The ring `LocallyConstant X ℤ` of locally constant integer-valued functions on a compact
space is generated as a ring by its idempotents, the characteristic functions of clopens. -/
theorem subring_closure_isIdempotentElem_eq_top :
    Subring.closure {e : LocallyConstant X ℤ | IsIdempotentElem e} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [eq_sum_intCast_mul_charFn f]
  exact Subring.sum_mem _ fun v _ ↦ Subring.mul_mem _ (intCast_mem _ v)
    (Subring.subset_closure (isIdempotentElem_charFn ℤ _))

variable {R : Type*} [CommRing R]

/-- Every prime ideal of the ring of locally constant functions on a compact space lies over a
point `x`: it contains the kernel of the evaluation at `x`. -/
theorem exists_ker_evalRingHom_le (p : Ideal (LocallyConstant X R)) [hp : p.IsPrime] :
    ∃ x : X, RingHom.ker (evalRingHom (Y := R) x) ≤ p := by
  by_contra! h
  choose f hf hfp using fun x ↦ SetLike.not_le_iff_exists.mp (h x)
  have hU : ∀ x, IsClopen {y | f x y = 0} := fun x ↦ (f x).isLocallyConstant.isClopen_fiber 0
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ {y | f x y = 0})
    (fun x ↦ (hU x).isOpen) (fun y _ ↦ Set.mem_iUnion.mpr ⟨y, hf y⟩)
  have he : ∀ x, charFn R (hU x) ∈ p := fun x ↦ by
    have : f x * charFn R (hU x) = 0 := by
      ext y
      by_cases hy : f x y = 0 <;> simp [coe_charFn, hy]
    exact (hp.mem_or_mem (this ▸ p.zero_mem)).resolve_left (hfp x)
  have hprod : ∏ x ∈ t, (1 - charFn R (hU x)) = 0 := by
    ext y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    rw [← coeFnRingHom_apply, map_prod, Finset.prod_apply, coe_zero, Pi.zero_apply]
    refine Finset.prod_eq_zero hx ?_
    change (1 : R) - charFn R (hU x) y = 0
    rw [coe_charFn, Set.indicator_of_mem hy, Pi.one_apply, sub_self]
  have := congrArg (Ideal.Quotient.mk p) hprod
  rw [map_prod, map_zero] at this
  simp only [map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (he _), sub_zero,
    Finset.prod_const_one] at this
  exact one_ne_zero this

omit [CompactSpace X] in
/-- Let `π : Y → X` be continuous and `p` a prime ideal of `LocallyConstant X R` lying over
`x = π y`. Then `p` is the preimage under `π^* : LocallyConstant X R → LocallyConstant Y R` of a
prime ideal of `LocallyConstant Y R`, namely of `ev_y⁻¹(ev_x(p))`. -/
theorem exists_isPrime_comap_comapRingHom_eq {Y : Type*} [TopologicalSpace Y] (π : C(Y, X))
    (p : Ideal (LocallyConstant X R)) [p.IsPrime] {x : X}
    (hx : RingHom.ker (evalRingHom (Y := R) x) ≤ p) {y : Y} (hy : π y = x) :
    ∃ q : Ideal (LocallyConstant Y R), q.IsPrime ∧
      Ideal.comap (comapRingHom (Z := R) π) q = p := by
  have hs : Function.Surjective (evalRingHom (Y := R) x) := fun r ↦ ⟨const X r, rfl⟩
  have := Ideal.map_isPrime_of_surjective hs hx
  refine ⟨Ideal.comap (evalRingHom y) (Ideal.map (evalRingHom (Y := R) x) p),
    Ideal.IsPrime.comap _, ?_⟩
  have : (evalRingHom (Y := R) y).comp (comapRingHom (Z := R) π) = evalRingHom x := by
    ext g
    simp [hy]
  rw [Ideal.comap_comap, this, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hx]

end Compact

end LocallyConstant
