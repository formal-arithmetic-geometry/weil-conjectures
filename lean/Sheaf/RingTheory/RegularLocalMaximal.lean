/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.GRing

/-!
# Regular ring maps are local on the target

Source: Stacks Project, More on Algebra, Lemma 07C0
(blueprint: lem-weil-pbc-regular-local-maximal).
-/

@[expose] public section

universe u v

namespace RingHom

/-- For a ring map with Noetherian target, regularity is equivalent to regularity of all
induced maps on prime localizations, and also to regularity at all maximal target ideals.
Source: Stacks Project, More on Algebra, Lemma 07C0
(blueprint: lem-weil-pbc-regular-local-maximal).

Proof:
1. Flatness is equivalent to flatness of all induced local maps, by
   `lem-weil-pbc-flat-map-local-criterion` (Stacks 00HT).
2. At a prime `q` above `p`, the closed fibre of the local map is a localization of the
   global fibre at `p`. This identification commutes with finite purely inseparable residue
   field extensions (`def-weil-pbc-g-ring`, `def-weil-pbc-localization-at-prime`). A Noetherian
   fibre ring is regular exactly when its prime localizations are regular local rings, by
   `lem-weil-pbc-regular-ring-local-criterion`. The same argument for each prime of the source
   local ring gives the equivalence of global regularity and the prime-local condition.
3. The prime-local condition includes the maximal-local condition. Conversely, put each
   target prime inside a maximal ideal. The map at that prime is obtained by further
   localization of the map at the maximal ideal. Apply the fibre-localization description
   and `lem-weil-pbc-regular-ring-local-criterion` again to obtain regularity there. Together
   with step 1, this gives the maximal-local equivalence. -/
theorem isRegular_iff_localRingHom_prime_and_maximal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) :
    (f.IsRegular ↔ ∀ (q : Ideal S) [q.IsPrime],
      (Localization.localRingHom (q.comap f) q f rfl).IsRegular) ∧
    (f.IsRegular ↔ ∀ (m : Ideal S) [m.IsMaximal],
      (Localization.localRingHom (m.comap f) m f rfl).IsRegular) := by
  sorry

end RingHom
