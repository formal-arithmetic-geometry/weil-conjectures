/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.SingularIdealsRelativeBound
import WeilConjectures.RingTheory.SingularIdealsAbsoluteBound

/-! # From an annihilator bound to singular-ideal comparisons

For a finitely presented tower `R → D → B` over a Noetherian ring `R`, we show that an
annihilator bound for `π ∈ R` forces the singular ideals `H_{B/D}` and `H_{B/R}` to contain the
extension of `H_{D/R}`.

## References

* [Stacks, Tag 07CT]
-/

@[expose] public section

universe u v w

namespace Algebra

/-- For a finitely presented tower `R → D → B`, an annihilator bound makes the relative and
absolute singular ideals `H_{B/D}` and `H_{B/R}` contain the extension of `H_{D/R}`. -/
theorem singularIdeals_of_annihilator_bound
    (R : Type u) (D : Type v) (B : Type w)
    [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R D]
    (dB : D →ₐ[R] B)
    (hfp : @FinitePresentation D B _ _ dB.toRingHom.toAlgebra)
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hbound : Ideal.span (dB ''
      {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
        r * algebraMap R D π * x = 0}) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra) :
    Ideal.map dB.toRingHom (singularIdeal R D) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra ∧
    Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  exact ⟨singularIdeal_map_le_relative_of_annihilator_bound R D B dB hfp π hR hbound,
    singularIdeal_map_le_absolute_of_annihilator_bound R D B dB hfp π hR hbound⟩

end Algebra
