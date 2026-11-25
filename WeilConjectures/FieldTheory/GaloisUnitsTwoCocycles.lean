/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
import Mathlib.Tactic.Abel

/-!
# Explicit continuous two-cocycles with separable-closure unit coefficients

Continuous inhomogeneous two-cocycles of the absolute Galois group with values in the units of
the separable closure, and their classes modulo continuous coboundaries.

## Main definitions

- `Field.GaloisUnitsTwoCocycle`: continuous inhomogeneous two-cocycles.
- `Field.GaloisUnitsTwoCocycleClasses`: two-cocycles modulo continuous coboundaries.

## Implementation details

This explicit quotient uses jointly continuous functions on `G × G` and the usual inhomogeneous
differential; it does not use étale sheaf cohomology or Mathlib's homogeneous continuous
cohomology.

## References

* [Stacks Project, Section 0DVG](https://stacks.math.columbia.edu/tag/0DVG), inhomogeneous
  differential
-/

@[expose] public section

universe u

namespace Field

variable (K : Type u) [Field K]

/-- Continuous inhomogeneous two-cocycles for the absolute Galois action.
These are the continuous `c : G × G → (K^sep)ˣ` with `d₂ c = 0`, i.e.
`g • c(h, i) - c(gh, i) + c(g, hi) - c(g, h) = 0` in additive notation. -/
def GaloisUnitsTwoCocycle : Type u :=
  { c : (Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K)) →
      (galoisUnitsTopRep K) //
    Continuous c ∧ ∀ g h i,
      (galoisUnitsTopRep K).ρ g (c (h, i)) - c (g * h, i) +
        c (g, h * i) - c (g, h) = 0 }

/-- Two continuous cocycles differ by the coboundary of a continuous one-cochain. -/
def galoisUnitsTwoCocycleRel (c d : GaloisUnitsTwoCocycle K) : Prop :=
  ∃ b : Gal(SeparableClosure K/K) → (galoisUnitsTopRep K),
    Continuous b ∧ ∀ g h,
      d.val (g, h) = c.val (g, h) +
        ((galoisUnitsTopRep K).ρ g (b h) - b (g * h) + b g)

/-- The setoid on continuous two-cocycles given by differing by a continuous coboundary. -/
def galoisUnitsTwoCocycleSetoid : Setoid (GaloisUnitsTwoCocycle K) where
  r := galoisUnitsTwoCocycleRel K
  iseqv := {
    refl := by
      intro c
      refine ⟨fun _ ↦ 0, continuous_const, ?_⟩
      intro g h
      simp
    symm := by
      intro c d hcd
      obtain ⟨b, hb, hbd⟩ := hcd
      refine ⟨fun g ↦ -b g, hb.neg, ?_⟩
      intro g h
      rw [hbd g h]
      simp only [map_neg]
      abel
    trans := by
      intro c d e hcd hde
      obtain ⟨b, hb, hbd⟩ := hcd
      obtain ⟨a, ha, hae⟩ := hde
      refine ⟨fun g ↦ b g + a g, hb.add ha, ?_⟩
      intro g h
      rw [hae g h, hbd g h]
      simp only [map_add]
      abel }

/-- Continuous two-cocycles modulo continuous coboundaries. -/
def GaloisUnitsTwoCocycleClasses : Type u := Quotient (galoisUnitsTwoCocycleSetoid K)

end Field
