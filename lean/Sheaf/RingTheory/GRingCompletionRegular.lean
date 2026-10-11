/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.RingTheory.GRing

/-!
# Completion maps of G-rings are regular

Source: Stacks Project, More on Algebra, Lemma Tag 0AH2 (Matsumura, Theorem 79)
(blueprint: lem-weil-pbc-g-ring-completion-regular).
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The canonical map from a G-ring to its completion along any ideal is regular.
Source: Stacks Project, More on Algebra, Lemma Tag 0AH2
(blueprint: lem-weil-pbc-g-ring-completion-regular).

Proof:
1. The G-ring hypothesis gives Noetherianity (`def-weil-pbc-g-ring`). The completion is
   Noetherian (`lem-weil-pbc-adic-completion-noetherian`), and its canonical map is flat
   (`lem-weil-pbc-noetherian-completion-flat`). The ideal is finitely generated.
2. By `lem-weil-pbc-regular-local-maximal`, it suffices to check regularity after localizing
   at every maximal ideal m' of the completion. Write m for its inverse image and B for
   the localization at m' (`def-weil-pbc-localization-at-prime`).
3. The projection to A/I is surjective with kernel I times the completion, and the
   completion is complete for that extended ideal (`lem-weil-pbc-adic-completion-mod-ideal`).
   That ideal lies in m' by `lem-weil-pbc-adic-complete-jacobson-radical`.
4. The projection identifies the quotients by m and m', so m is maximal, contains I,
   and m' is the extension of m. The induced residue-field map is an isomorphism
   (`lem-weil-pbc-adic-completion-mod-ideal`).
5. The localized map from A_m to B is flat and local between Noetherian local rings
   (`lem-weil-pbc-flat-local-ring-maps`). Its extended maximal ideal is the maximal
   ideal of B, and its residue-field map is the isomorphism from step 4
   (`def-weil-pbc-localization-at-prime`).
6. The localized map induces an isomorphism between the maximal-ideal-adic completions
   of A_m and B, commuting with their canonical maps
   (`lem-weil-pbc-flat-local-completion-iso`, `def-weil-pbc-adic-completion`).
7. The completion map of A_m is regular by `def-weil-pbc-g-ring`. Transporting flatness
   and the Noetherian, geometrically regular fibres along the isomorphism of step 6
   shows that the composite from A_m to the completion of B is regular.
8. The completion map of B is faithfully flat, hence flat and surjective on spectra
   (`lem-weil-pbc-local-completion-faithfully-flat`).
9. Descend regularity to A_m to B by `lem-weil-pbc-regular-permanence`. As m' was arbitrary,
   step 2 proves regularity of the original completion map. -/
theorem isRegular_of_isGRing (A : Type u) [CommRing A] (I : Ideal A) (hA : IsGRing A) :
    RingHom.IsRegular (algebraMap A (AdicCompletion I A)) := by
  sorry

end AdicCompletion
