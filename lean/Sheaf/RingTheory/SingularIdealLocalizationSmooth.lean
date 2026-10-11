/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.RingTheory.SingularIdeal

/-!
# Smoothness after localizing at an element of the singular ideal

Source: Stacks Project, Smoothing Ring Maps, Lemma 07EU (lemma-final-solve)
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth).
-/

universe u v

namespace Algebra

/-- If an element belongs to the singular ideal, its principal localization is smooth.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07EU (lemma-final-solve), using
Definition 07C5 (definition-singular-ideal) and Algebra Lemma 00TC.
(blueprint: lem-weil-pbc-singular-ideal-localization-smooth).

Proof: Membership in the radical gives a finite relation expressing a power of the
 element as a combination of smooth localization elements. After localizing at the
given element these elements generate the unit ideal. Localizing each one further is
smooth because principal localization preserves smoothness and localizations commute.
Smoothness is then local on this finite principal cover, including the empty cover of
the zero localization.
-/
theorem smooth_localization_of_mem_singularIdeal
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (hf : f ∈ singularIdeal R A) :
    Smooth R (Localization.Away f) := by
  sorry

end Algebra
