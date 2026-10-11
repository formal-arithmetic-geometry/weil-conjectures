/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.SerreConditions
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Ascent of Serre's condition (S_k) along flat maps

Source: Stacks Project, Algebra, Lemma Tag 0339 (lemma-Sk-goes-up)
(blueprint: lem-weil-pbc-serre-sk-goes-up).

## Main statements

- `RingHom.isSerreS_of_flat`: property (S_k) ascends along a flat map with
  Noetherian source and target and (S_k) fibres.
-/

universe u v

namespace RingHom

/-- Property `(S_k)` ascends along a flat map with `(S_k)` fibres.
Source: Stacks Project, Algebra, Lemma Tag 0339 (lemma-Sk-goes-up),
(blueprint: lem-weil-pbc-serre-sk-goes-up).

Proof:
1. Fix a prime `q` of `S` and set `p = φ⁻¹(q)`, where `φ = algebraMap R S`.
   The induced map `Rₚ → S_q` is flat and local, with Noetherian source and target
   (`lem-weil-pbc-flat-local-ring-maps`). By the Serre definition we must prove
   `depth(S_q) ≥ min(k, dim(S_q))` (`def-weil-pbc-serre-conditions-rk-sk`).
2. The maximal ideal of `Rₚ` is `p Rₚ`; its extension to `S_q` is `p S_q`, since
   denominators outside `p` map to units. Thus the closed fibre is `S_q / p S_q`
   (`def-weil-pbc-localization-at-prime`).
3. The flat local depth formula gives
   `depth(S_q) = depth(Rₚ) + depth(S_q / p S_q)`
   (`lem-weil-pbc-flat-local-depth-formula`, Stacks Tag 0337).
4. The dimension formula gives `dim(S_q) ≤ dim(Rₚ) + dim(S_q / p S_q)`
   (`lem-weil-pbc-flat-height-formula`, Tags 00OM and 00ON).
5. The fibre `C = p.Fiber S` is Noetherian (`lem-weil-pbc-fibre-ring-noetherian`).
   The prime of `C` corresponding to `q` (`lem-weil-pbc-fibre-ring-primes-bijection`)
   has localization isomorphic to `S_q / p S_q`
   (`lem-weil-pbc-fibre-ring-local-ring-iso`). The fibre hypothesis and invariance
   of depth and dimension under ring isomorphism yield
   `depth(S_q / p S_q) ≥ min(k, dim(S_q / p S_q))`
   (`def-weil-pbc-serre-conditions-rk-sk`, `def-weil-pbc-depth`).
6. The base hypothesis yields `depth(Rₚ) ≥ min(k, dim(Rₚ))`
   (`def-weil-pbc-serre-conditions-rk-sk`).
7. For `a = dim(Rₚ)` and `b = dim(S_q / p S_q)`, we have
   `min(k, a) + min(k, b) ≥ min(k, a + b)`: if either summand's dimension is at
   least `k`, the left side is at least `k`; otherwise it equals `a + b`.
   Combining steps 3--6 proves the required bound at every `q`, hence `(S_k)`.

The arbitrary ring map is encoded by `[Algebra R S]` and `algebraMap R S`.
Every ring homomorphism gives such an algebra structure via `RingHom.toAlgebra`.
The existential Noetherian witness makes the fibre predicate well-typed and
asserts its existence, rather than making the predicate conditional on it.
-/
theorem isSerreS_of_flat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (k : ℕ) (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ (p : Ideal R) [p.IsPrime],
      ∃ (_ : IsNoetherianRing (p.Fiber S)), Ring.IsSerreS (p.Fiber S) k)
    (hR : Ring.IsSerreS R k) :
    Ring.IsSerreS S k := by
  sorry

end RingHom
