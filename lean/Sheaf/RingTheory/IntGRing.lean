/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.RingTheory.GRing

/-!
# The integers are a G-ring

Source: Stacks Project, More on Algebra, Proposition 07PX, item (3)
(blueprint: lem-weil-pbc-z-g-ring).
-/

namespace Int

/-- The ring of integers is a G-ring. Source: Stacks Project, More on Algebra,
Proposition 07PX, item (3) (blueprint: lem-weil-pbc-z-g-ring).

Proof:
1. The integers are Noetherian. Their localization at the zero prime is the field of
   rationals, and at every nonzero prime it is a discrete valuation ring
   (`lem-weil-pbc-z-localizations-dvr`). By `def-weil-pbc-g-ring`, it suffices to check
   regularity of the completion map for each of these localizations.
2. At the zero prime the maximal ideal is zero and completion is the field itself.
   Its identity map is flat, and its only fibre is a field, hence geometrically regular:
   after any finite purely inseparable field extension the fibre is again a field
   (`lem-weil-pbc-field-regular-ring`). Thus this completion map is regular.
3. At every nonzero prime the localization is a Noetherian local discrete valuation
   ring with fraction field of characteristic zero. Its completion map is regular by
   `lem-weil-pbc-dvr-completion-regular`: completion is flat (Stacks 00MB) and is a DVR
   (Stacks 0AP1); the generic fibre is its fraction field, geometrically regular over
   the rationals in characteristic zero, and the closed fibre is the residue field.
4. These cases cover every prime of the integers. Hence all completion maps in the
   definition of `IsGRing` are regular, giving the claim. -/
theorem isGRing : IsGRing ℤ := by
  sorry

end Int
