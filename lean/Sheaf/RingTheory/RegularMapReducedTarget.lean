/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Sheaf.RingTheory.SerreCriterionReduced
import Sheaf.RingTheory.RegularityRkGoesUp
import Sheaf.RingTheory.SerreSkGoesUp

/-!
# Reducedness ascends along regular maps of Noetherian rings

Source: Stacks Project, More on Algebra, Lemma 15.43.1 (Tag 07QK),
`lemma-reduced-goes-up` (blueprint: lem-exc-regular-map-reduced-target).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A regular homomorphism of Noetherian commutative rings with reduced source has reduced
codomain. Source: Stacks Project, More on Algebra, Lemma 15.43.1 (Tag 07QK),
`lemma-reduced-goes-up` (blueprint: lem-exc-regular-map-reduced-target).

Proof:
1. Unpack `def-weil-pbc-g-ring`: the map is flat, and every residue-field fibre is
   Noetherian and geometrically regular. The identity extension of its residue field is
   finite and purely inseparable. Base change along it is canonically the fibre itself,
   via `a ⊗ x ↦ a • x`, with inverse `x ↦ 1 ⊗ x`. Thus the fibre is regular, and all its
   prime localizations are regular local rings (`def-weil-regular-scheme`).
2. These local rings are domains by `lem-sc-regular-local-domain`. Every domain is reduced:
   induction on a positive nilpotence exponent, using absence of zero divisors, kills a
   nilpotent element. Prime localizations jointly detect zero, so each fibre is reduced
   (`lem-weil-pbc-prime-localizations-jointly-injective`). This also covers a zero fibre,
   whose prime spectrum is empty.
3. Apply `lem-weil-pbc-serre-criterion-reduced` to the Noetherian reduced source and to each
   Noetherian reduced fibre. All satisfy both `(R₀)` and `(S₁)`.
4. Apply `lem-weil-pbc-regularity-rk-goes-up` at index zero, using flatness, both Noetherian
   hypotheses and the base and fibre `(R₀)` conditions. The target satisfies `(R₀)`.
   Apply `lem-weil-pbc-serre-sk-goes-up` at index one with the same flatness and Noetherian
   hypotheses and the base and fibre `(S₁)` conditions. The target satisfies `(S₁)`.
5. Apply the converse of `lem-weil-pbc-serre-criterion-reduced` to the Noetherian target
   with these two conditions. It is reduced. No finite-type or smoothness assumption enters.
-/
theorem isReduced_of_isRegular {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsReduced A]
    (φ : A →+* B) (hφ : φ.IsRegular) : IsReduced B := by
  sorry

end RingHom
