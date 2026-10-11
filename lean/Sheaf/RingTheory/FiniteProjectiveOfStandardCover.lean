/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite projectivity from a finite standard-open free cover

Source: Stacks Project, Algebra, Lemma 10.78.2, Tag 00NX, implication (7) ⇒ (2)
(blueprint: lem-sc-affine-standard-cover-finite-projective).
-/

universe u v

namespace Module

/-- A module whose localizations on a finite standard-open cover are finite free is
finite projective. Source: Stacks Project, Algebra, Tag 00NX, Lemma 10.78.2, (7) ⇒ (2).
(blueprint: lem-sc-affine-standard-cover-finite-projective)

Proof: the finite standard-open cover criterion applied to the family `f` first gives
finite presentation and flatness (`lem-sc-affine-standard-cover-finite-presentation-flat`):
finite freeness
implies finite presentation locally, which descends along the standard-open cover;
flatness is likewise checked locally. A finitely presented flat module is projective
(`lem-weil-pbc-finitely-presented-flat-module-projective`). Finite presentation implies
finite generation, so this gives both finiteness and projectivity, as required by
`def-weil-pbc-projective-module`. No common rank for the local free modules is assumed. -/
theorem finite_projective_of_localizationAway_free
    {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
    {r : ℕ} (f : Fin r → R) (hspan : Ideal.span (Set.range f) = ⊤)
    (hlocal : ∀ i : Fin r,
      Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) N) ∧
      Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) N)) :
    Module.Finite R N ∧ Module.Projective R N := by
  sorry

end Module
