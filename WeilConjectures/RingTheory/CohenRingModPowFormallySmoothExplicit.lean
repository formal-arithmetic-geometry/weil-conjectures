/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothCore
import Mathlib.Algebra.Algebra.ZMod

/-!
# Square-zero lifting for a Cohen ring modulo a prime power

For a Cohen ring `Λ` and `n ≥ 1`, every ring map from `Λ / (p ^ n)` to `D / J`, with
`p ^ n = 0` in `D` and `J ^ 2 = 0`, lifts to a ring map into `D`
(`IsDiscreteValuationRing.cohenRing_mod_pow_formallySmooth_explicit`).

## Implementation details

The canonical `ZMod (p ^ n)`-algebra structures on `Λ / (p ^ n)` and `D` make every ring map
`ZMod (p ^ n)`-linear, so the statement follows from formal smoothness of `Λ / (p ^ n)` over
`ZMod (p ^ n)`. The argument works in any target universe and when `D` is the zero ring.

## References

* [Stacks, Tag 0329]
-/

@[expose] public section
universe u v
namespace IsDiscreteValuationRing
/-- The explicit square-zero lifting property of a Cohen ring modulo a prime power: if
`p ^ n = 0` in `D` and `J ^ 2 = 0`, every ring map `Λ / (p ^ n) → D / J` lifts to `D`. -/
theorem cohenRing_mod_pow_formallySmooth_explicit
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ (D : Type v) [CommRing D], (p : D) ^ n = 0 →
      ∀ (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D ⧸ J),
          ∃ f : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D,
            (Ideal.Quotient.mk J).comp f = g := by
  let Q := Λ ⧸ Ideal.span {(p : Λ) ^ n}
  have hQ : ((p ^ n : ℕ) : Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _) (p ^ n), Nat.cast_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  let : Algebra (ZMod (p ^ n)) Q := ZMod.algebra' Q (ringChar Q) (ringChar.dvd hQ)
  let : Algebra.FormallySmooth (ZMod (p ^ n)) Q :=
    cohenRing_mod_pow_formallySmooth_core p Λ hΛ n hn
  intro D _ hD J hJ g
  let : Algebra (ZMod (p ^ n)) D :=
    ZMod.algebra' D (ringChar D) (ringChar.dvd (by simpa using hD))
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩
    ({ toRingHom := g, commutes' := by
        intro r
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
        simp } : Q →ₐ[ZMod (p ^ n)] D ⧸ J)
  exact ⟨f.toRingHom, congrArg AlgHom.toRingHom hf⟩
end IsDiscreteValuationRing
