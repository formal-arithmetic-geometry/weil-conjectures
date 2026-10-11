/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.RingTheory.SerreConditions
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Ascent of Serre regularity in codimension

Source: Stacks Project, Algebra, Lemma Tag 033A (lemma-Rk-goes-up)
(blueprint: lem-weil-pbc-regularity-rk-goes-up).

## Main statement

- `regularity_rk_goes_up`: property `(R_k)` ascends along a flat map with
  Noetherian fibres satisfying `(R_k)`.
-/

universe u v

namespace RingHom

/-- For a flat homomorphism of Noetherian rings, `(R_k)` ascends when every
fibre is Noetherian and satisfies `(R_k)`. Source: Stacks Project, Algebra,
Lemma Tag 033A (blueprint: lem-weil-pbc-regularity-rk-goes-up).

Proof:
1. Fix a prime `q` of `S` of height at most `k`, and put `p = φ⁻¹(q)`,
   where `φ = algebraMap R S`.
   The induced map `Rₚ → S_q` is a flat local map of Noetherian local rings
   (`lem-weil-pbc-flat-local-ring-maps`).
2. The flat dimension formula gives
   `dim S_q = dim Rₚ + dim (S_q / p S_q)`, so both summands are at most `k`
   (`lem-weil-pbc-flat-height-formula`).
3. The height bound and `(R_k)` for `R` imply that `Rₚ` is regular
   (`def-weil-pbc-serre-conditions-rk-sk`).
4. The fibre ring is Noetherian (`lem-weil-pbc-fibre-ring-noetherian`).
   The prime corresponding to `q` (`lem-weil-pbc-fibre-ring-primes-bijection`)
   has localization isomorphic to `S_q / p S_q`
   (`lem-weil-pbc-fibre-ring-local-ring-iso`, Stacks Remark 0H9M).
   Its height is at most `k` by step 2 and invariance of dimension under
   isomorphism. The fibre hypothesis therefore makes this quotient regular.
5. The maximal ideal of `Rₚ` is `p Rₚ`
   (`def-weil-pbc-localization-at-prime`); its extension to `S_q` is `p S_q`,
   since denominators outside `p` map to units. Thus this quotient is the
   closed fibre of `Rₚ → S_q`.
6. Regularity of the base and closed fibre implies regularity of `S_q`
   (`lem-weil-pbc-flat-over-regular-with-regular-fibre`, Stacks Tag 031E).
   Since `q` was arbitrary, `S` satisfies `(R_k)`.

The algebra structure on `S` is the instance `[Algebra R S]`, and the ring map
of the source is `algebraMap R S`; the fibre rings `p.Fiber S` are formed with it.
-/
theorem regularity_rk_goes_up {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] (k : ℕ)
    (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ (p : Ideal R) [p.IsPrime],
      ∃ (_ : IsNoetherianRing (p.Fiber S)), Ring.IsSerreR (p.Fiber S) k)
    (hR : Ring.IsSerreR R k) : Ring.IsSerreR S k := by
  sorry

end RingHom
