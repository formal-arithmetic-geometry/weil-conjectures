/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-!
# Finite presentation and flatness from a finite standard-open free cover

Source: Stacks Project, Algebra, Lemma Tag 00NX, implications (7) → (4) → (5) → (1),
using Tags 00EO (3) and 00HT (5)
(blueprint: lem-sc-affine-standard-cover-finite-presentation-flat).
-/

universe u v

namespace Module

/-- A module with finite free localizations on a finite standard-open cover is finitely
presented and flat. Source: Stacks Project, Algebra, Tag 00NX, (7) → (4) → (5) → (1),
with Tags 00EO (3) and 00HT (5)
(blueprint: lem-sc-affine-standard-cover-finite-presentation-flat).

Proof: Let `s` be the range of the finite family `f`. Its span is the unit ideal by hypothesis.
For each member of `s`, finite freeness gives finite presentation and flatness of the localized
module over the localized ring
[lem-sc-affine-standard-cover-finite-free-local-fp-flat]. Apply finite-presentation descent on
this unit-ideal cover [lem-sc-affine-standard-cover-finite-presentation-localization-span] to
obtain finite presentation over `R`. The localized modules are also flat over `R`, since the
localized rings are flat over `R`. Apply flatness descent on the same cover
[lem-sc-affine-standard-cover-flat-localization-span] to obtain flatness over `R`. -/
theorem finitePresentation_and_flat_of_finite_free_standard_cover
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (f : Fin r → R) (hspan : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) N) ∧
      Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) N)) :
    Module.FinitePresentation R N ∧ Module.Flat R N := by sorry

end Module
