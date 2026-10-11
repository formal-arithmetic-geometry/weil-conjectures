/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Normality ascends along flat maps with normal fibres

Source: Stacks Project, Algebra, Lemma 10.163.8, Tag 0C22
(blueprint: lem-weil-pbc-flat-normal-fibres-noetherian-normal).
-/

universe u v

namespace RingHom

/-- A flat map of Noetherian rings with normal fibres and normal source has normal target.
Source: Stacks Project, Algebra, Tag 0C22
(blueprint: lem-weil-pbc-flat-normal-fibres-noetherian-normal).

Proof: Each fibre is Noetherian because it is a quotient of a localization of `S`
(`lem-weil-pbc-fibre-ring-noetherian`). Serre's criterion, Tag 031S
(`lem-weil-pbc-serre-criterion-normal`), gives `(R₁)` and `(S₂)` for `R` and every fibre.
Flat ascent of `(S₂)`, Tag 0339 (`lem-weil-pbc-serre-sk-goes-up`), gives `(S₂)` for `S`.
Flat ascent of `(R₁)`, Tag 033A (`lem-weil-pbc-regularity-rk-goes-up`), gives `(R₁)` for `S`.
Finally apply Serre's criterion again to the Noetherian ring `S` to conclude normality.
Normality means that every prime localization is an integrally closed domain, including
when a ring or a fibre is zero (in which case there are no prime ideals). -/
theorem normal_of_flat_normal_fibers {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (hflat : φ.Flat)
    (hfibres : letI : Algebra R S := φ.toAlgebra
      ∀ (p : Ideal R) [p.IsPrime], ∀ (q : Ideal (p.Fiber S)) [q.IsPrime],
        IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  sorry

end RingHom
