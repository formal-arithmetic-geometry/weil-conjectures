/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
import Mathlib.RingTheory.Localization.Basic

/-!
# Singular ideals under algebra equivalences

An `R`-algebra equivalence `A ≃ₐ[R] B` maps the singular ideal of `A` into the singular ideal
of `B`.

## References

* [Stacks, Tag 07C5]
-/

@[expose] public section

universe u v w

namespace Algebra

/-- An algebra equivalence carries the singular ideal into the singular ideal. -/
theorem singularIdeal_map_equiv_le
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) : Ideal.map e.toRingHom (singularIdeal R A) ≤ singularIdeal R B := by
  unfold singularIdeal
  refine (Ideal.map_radical_le e.toRingHom).trans (Ideal.radical_mono ?_)
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro a ha
  apply Ideal.subset_span
  change Smooth R (Localization.Away (e a))
  have : Smooth R (Localization.Away a) := ha
  let E : Localization.Away a ≃ₐ[R] Localization.Away (e a) :=
    IsLocalization.algEquivOfAlgEquiv _ _ e (Submonoid.map_powers e a)
  exact Smooth.of_equiv E

end Algebra
