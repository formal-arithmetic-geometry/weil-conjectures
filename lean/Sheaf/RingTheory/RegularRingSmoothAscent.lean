/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity ascends along smooth ring maps

Source: Stacks Project, Algebra, Lemma 07NF
(blueprint: lem-weil-pbc-regular-ring-smooth-ascent).
-/

universe u v

namespace Algebra

/-- A smooth algebra over a regular ring is regular.
Source: Stacks Project, Algebra, Lemma 07NF
(blueprint: lem-weil-pbc-regular-ring-smooth-ascent).

Proof:
1. R is Noetherian by def-weil-regular-scheme. Smoothness gives finite presentation and
   hence finite type by def-weil-pbc-smooth-ring-map, so S is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian (Stacks 00FN).
2. The map R → S is flat by lem-weil-pbc-smooth-ring-map-flat (Stacks 00TA).
3. For each prime p of R, the residue-field fibre is smooth by base change (Stacks 00T4).
   Every prime localization of this fibre is regular local by
   lem-weil-pbc-smooth-fibre-regular-local (Stacks 00TT). Thus the fibres satisfy (R_k)
   for every nonnegative integer k.
4. R satisfies every (R_k) by regularity. Applying lem-weil-pbc-regularity-rk-goes-up
   (Stacks 033A) to the Noetherian rings R and S, the flat map, and these fibre properties
   shows that S satisfies every (R_k).
5. Each prime localization of S has finite dimension since it is Noetherian local.
   Choose k at least that dimension and apply (R_k) to see that it is regular local.
   Together with Noetherianity of S, this is regularity by def-weil-regular-scheme
   (Stacks 00OD).
-/
theorem isRegularRing_of_smooth
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Smooth R S] [IsRegularRing R] : IsRegularRing S := by
  sorry

end Algebra
