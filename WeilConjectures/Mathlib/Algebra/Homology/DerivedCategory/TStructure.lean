/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# Objects of a derived category with homology concentrated in an interval

For an abelian category `C`, this file records the property that an object of `D(C)` has
homology in degrees `[a, b]` only, expressed through the canonical t-structure
`DerivedCategory.TStructure.t` so that the whole t-structure API applies to it.

## Main definitions

- `DerivedCategory.homologyConcentratedIn`: homology concentrated in `[a, b]`.

## Main statements

- `DerivedCategory.exists_homologyConcentratedIn_iff_bounded`: an object is bounded exactly
  when its homology is concentrated in some interval.

-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of `D(C)` has *homology concentrated in `[a, b]`* if it is both `≥ a` and `≤ b`
for the canonical t-structure `DerivedCategory.TStructure.t`, that is, if its homology
objects vanish outside the interval `[a, b]`. -/
def homologyConcentratedIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b

lemma homologyConcentratedIn_iff (a b : ℤ) (M : DerivedCategory C) :
    homologyConcentratedIn a b M ↔ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b :=
  Iff.rfl

/-- Widening the interval preserves homology concentration. -/
lemma homologyConcentratedIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : DerivedCategory C} (hM : homologyConcentratedIn a b M) :
    homologyConcentratedIn a' b' M := by
  obtain ⟨h₁, h₂⟩ := hM
  exact ⟨TStructure.t.isGE_of_ge M a' a ha, TStructure.t.isLE_of_le M b b' hb⟩

/-- An object of `D(C)` is bounded exactly when its homology is concentrated in some
interval. -/
lemma exists_homologyConcentratedIn_iff_bounded (M : DerivedCategory C) :
    (∃ a b : ℤ, homologyConcentratedIn a b M) ↔ TStructure.t.bounded M := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩

end DerivedCategory
