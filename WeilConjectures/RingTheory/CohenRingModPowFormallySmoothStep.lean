/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.RingTheory.CohenRing
import Mathlib.RingTheory.Smooth.Quotient
import WeilConjectures.RingTheory.CohenRingModPowFlat
import WeilConjectures.RingTheory.ModPowFormallySmoothReduction

/-!
# Formal smoothness of a Cohen ring modulo a prime power: the induction step

For a Cohen ring `Λ` and `n ≥ 1`, formal smoothness of `Λ / (p ^ n)` over `ℤ / p ^ n` implies
formal smoothness of `Λ / (p ^ (n + 1))` over `ℤ / p ^ (n + 1)`
(`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_step`).

## Implementation details

Let `R = ℤ / p ^ (n + 1)`, `S = Λ / (p ^ (n + 1))` and `I = (p ^ n) ⊆ R`, so that `I ^ 2 = 0`.
A Cohen ring is torsion-free, hence flat, over `ℤ`, so `S` is flat over `R`. The reductions
`R / I` and `S / I S` are `ℤ / p ^ n` and `Λ / (p ^ n)`, and the flat square-zero quotient
criterion gives formal smoothness of `R → S`. The `ZMod`-algebra structures are unique, so the
conclusion holds for every such structure.

## References

* [Stacks, Tag 0329]
* [Stacks, Tag 031L]
-/

@[expose] public section

universe u

namespace IsDiscreteValuationRing

/-- The induction step for formal smoothness of a Cohen ring modulo a prime power: if
`Λ / (p ^ n)` is formally smooth over `ℤ / p ^ n` with `n ≥ 1`, then `Λ / (p ^ (n + 1))` is
formally smooth over `ℤ / p ^ (n + 1)`. -/
theorem cohenRing_mod_pow_formallySmooth_step
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n)
    (ih : ∀ [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})],
      Algebra.FormallySmooth (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})) :
    ∀ [Algebra (ZMod (p ^ (n + 1))) (Λ ⧸ Ideal.span {(p : Λ) ^ (n + 1)})],
      Algebra.FormallySmooth (ZMod (p ^ (n + 1)))
        (Λ ⧸ Ideal.span {(p : Λ) ^ (n + 1)}) := by
  intro inst
  let R := ZMod (p ^ (n + 1))
  let S := Λ ⧸ Ideal.span {(p : Λ) ^ (n + 1)}
  let f : R →+* S := algebraMap R S
  let I : Ideal R := Ideal.span {((p : R) ^ n)}
  let J : Ideal S := I.map f
  have : Module.Flat R S := cohenRing_mod_pow_flat p Λ hΛ (n + 1)
  have hsquare : I ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, ← pow_mul, Ideal.span_singleton_eq_bot]
    exact_mod_cast ZMod.natCast_pow_eq_zero_of_le p (show n + 1 ≤ n * 2 by omega)
  have hq := modPow_formallySmooth_reduction p Λ n (n + 1) (by omega) ih
  apply (RingHom.formallySmooth_algebraMap).mp
  apply RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero f
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
    (Ideal.Quotient.mk I) (Ideal.Quotient.mk J)
    (Ideal.quotientMap J f Ideal.le_comap_map)
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective
  · ext x
    rfl
  · simpa only [Ideal.mk_ker] using hsquare
  · simp only [Ideal.mk_ker]
    rfl
  · exact hq

end IsDiscreteValuationRing
