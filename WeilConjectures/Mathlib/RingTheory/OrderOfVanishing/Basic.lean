/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Invariance of the order of vanishing under ring isomorphisms

The order of vanishing `Ring.ord R x = length_R (R ⧸ (x))` and its extension `Ring.ordFrac` to a
fraction field are transported by ring isomorphisms.

## Main statements

- `Ring.ord_ringEquiv`: `ord_{R'} (e x) = ord_R x` for a ring isomorphism `e : R ≃+* R'`.
- `Ring.ordFrac_map_of_ringEquiv`: the same for `Ring.ordFrac`, along a compatible map of
  fraction fields.
-/

@[expose] public section

namespace Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing is invariant under ring isomorphisms. -/
lemma ord_ringEquiv (e : R ≃+* R') (x : R) : ord R' (e x) = ord R x := by
  let : Algebra R R' := e.toRingHom.toAlgebra
  have hs : Function.Surjective (algebraMap R R') := e.surjective
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (e : R →+* R') := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let φ : (R ⧸ Ideal.span {x}) ≃ₗ[R] (R' ⧸ Ideal.span {e x}) :=
    { Ideal.quotientEquiv _ _ e hI with
      map_smul' r y := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        change Ideal.Quotient.mk _ (e (r * y)) = Ideal.Quotient.mk _ (e r * e y)
        rw [map_mul] }
  rw [ord, ord, ← Module.length_eq_of_surjective (S := R) hs, φ.length_eq]

/-- The order of vanishing with values in `ℤᵐ⁰` is invariant under ring isomorphisms. -/
lemma ordMonoidWithZeroHom_ringEquiv [IsDomain R] [IsDomain R'] (e : R ≃+* R') (x : R) :
    ordMonoidWithZeroHom R' (e x) = ordMonoidWithZeroHom R x := by
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, map_zero]
  have hx' : e x ≠ 0 := (map_ne_zero_iff _ e.injective).2 hx
  rw [ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hx),
    ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hx'), ord_ringEquiv]

variable [IsNoetherianRing R] [KrullDimLE 1 R] [IsDomain R]
  [IsNoetherianRing R'] [KrullDimLE 1 R'] [IsDomain R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [Algebra R' K'] [IsFractionRing R K]
  [IsFractionRing R' K']

/-- `Ring.ordFrac` is invariant under a ring isomorphism `e : R ≃+* R'` together with a compatible
map of fraction fields `φ : K →+* K'`. -/
lemma ordFrac_map_of_ringEquiv (e : R ≃+* R') (φ : K →+* K')
    (hφ : ∀ r, φ (algebraMap R K r) = algebraMap R' K' (e r)) (z : K) :
    ordFrac R' (φ z) = ordFrac R z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
  change ordFrac R' (φ (IsLocalization.mk' K a b)) = ordFrac R (IsLocalization.mk' K a b)
  have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hb' : e b ≠ 0 := (map_ne_zero_iff _ e.injective).2 hb
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have h : φ (IsLocalization.mk' K a b) = algebraMap R' K' (e a) / algebraMap R' K' (e b) := by
    rw [IsFractionRing.mk'_eq_div, map_div₀, hφ, hφ]
  rw [h, map_div₀, IsFractionRing.mk'_eq_div, map_div₀]
  by_cases ha : a = 0
  · simp [ha]
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ e.injective).2 ha
  rw [ordFrac_eq_ord _ ha, ordFrac_eq_ord _ hb, ordFrac_eq_ord _ ha', ordFrac_eq_ord _ hb',
    ordMonoidWithZeroHom_ringEquiv, ordMonoidWithZeroHom_ringEquiv]

end Ring
