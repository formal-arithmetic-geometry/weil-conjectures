/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Quotient
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels

/-!
# Descending ideals and the quotient adic topology

Source: Stacks Project, Formal Deformation Theory, Tag 06SE
(`lemma-m-adic-topology`)
(blueprint: lem-sfb-artin-descending-ideal-adic-topology).

The sequence and all powers are indexed by positive natural numbers. Quotient ideals
are the images under the canonical quotient map, so no extra topology is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- A descending sequence containing the corresponding maximal-ideal powers is cofinal,
modulo its intersection, with the maximal-ideal powers of the quotient.

Source: Stacks Project, Formal Deformation Theory, Tag 06SE (`lemma-m-adic-topology`)
(blueprint: lem-sfb-artin-descending-ideal-adic-topology).

Proof:
1. For each positive `r`, the quotient `S / m^r` is Artinian by
   `lem-weil-pbc-noetherian-local-quotient-artinian-local`. The images of `Js n` therefore
   stabilize, at an index `N_r`; call their stable value `E_r`.
2. The quotient reductions restrict to surjections `E_(r+1) → E_r`: choose one index past
   both stabilization indices and use the images of that same ideal `Js n`.
3. By `CategoryTheory.tower_limit_projection_surjective`, part (a) of
   `lem-weil-pbc-tower-limit-exact-surjective-kernels`, the limit of the `E_r` surjects
   onto each `E_r`. Completeness (`def-weil-pbc-adic-completion`) identifies a compatible
   family with a unique element `f` of `S`.
4. Such an `f` is in `J`: for each positive `k`, choose `n ≥ N_k, k`. Then its residue
   modulo `m^k` lies in the image of `Js n ≤ Js k`. Hence `f ∈ Js k + m^k = Js k`,
   since `m^k ≤ Js k`. Given `x ∈ Js N_r`, lift its residue in `E_r` to this limit and
   to `f ∈ J`. Now `x - f ∈ m^r`, proving the first conclusion.
5. If `J` is proper, it lies in `m`; `lem-weil-pbc-quotient-local-structure` identifies
   the maximal ideal of `S/J` with the image of `m`. Ideal images commute with powers.
   Mapping `m^n ≤ Js n` gives the first cofinality inclusion. Mapping the conclusion
   of step 4 gives the second, since the image of `J` is zero. -/
theorem descending_ideals_quotient_adic
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Js : ℕ+ → Ideal S) (hdescending : Antitone Js)
    (hpowers : ∀ n : ℕ+, IsLocalRing.maximalIdeal S ^ (n : ℕ) ≤ Js n)
    (J : Ideal S) (hJ : J = ⨅ n : ℕ+, Js n) :
    (∀ r : ℕ+, ∃ N : ℕ+, Js N ≤ J ⊔ IsLocalRing.maximalIdeal S ^ (r : ℕ)) ∧
      (J ≠ ⊤ →
        (∀ n : ℕ+, ∃ r : ℕ+,
          (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk J) ^ (r : ℕ) ≤
            (Js n).map (Ideal.Quotient.mk J)) ∧
        (∀ r : ℕ+, ∃ n : ℕ+,
          (Js n).map (Ideal.Quotient.mk J) ≤
            (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk J) ^ (r : ℕ))) := by
  sorry

end Ideal
