/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Finiteness

/-! # A finite standard free cover for a finite projective module

Source: Stacks Project, Lemma Tag 00NX, (3)⇒(7), and Definition Tag 00NW
in Section Tag 00NV (blueprint: lem-weil-pbc-finite-projective-standard-free-cover).
-/

universe u v

namespace Module

/-- A finite projective module is finite free on a finite standard cover.
Source: Stacks Project, Lemma Tag 00NX, (3)⇒(7), and Definition Tag 00NW
(blueprint: lem-weil-pbc-finite-projective-standard-free-cover).
Proof, step 1: a direct summand of a finite free module is finite projective.
For each prime p, `lem-weil-pbc-finite-projective-prime-local-free` gives an element
fₚ outside p such that M localized away from fₚ is finite free.
Step 2: these principal opens cover Spec A. Apply quasi-compactness and the
principal-open/unit-ideal criterion in
`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` to choose finitely many of
them whose elements generate the unit ideal. Each chosen localization remains
finite free by step 1. The ranks may differ between members of the cover. -/
theorem exists_standardFreeCover_of_finite_projective
    (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] :
    ∃ (r : ℕ) (f : Fin r → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin r,
        Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) M) ∧
        Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) M) := by
  sorry

end Module
