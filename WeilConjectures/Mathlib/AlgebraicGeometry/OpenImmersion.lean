/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Open immersions respect open immersions on the right

The `MorphismProperty.RespectsRight` instance for open immersions of schemes, and the
emptiness of a fibre product over disjoint opens
(`AlgebraicGeometry.isEmpty_pullback_of_disjoint_range`).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

/-! ### Fibre products over disjoint opens -/

section DisjointRange

universe u

variable {U X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If `j` is an open immersion whose range is disjoint from the range of `f`, the fibre
product `V ×_X U` is empty. -/
lemma isEmpty_pullback_of_disjoint_range {V : Scheme.{u}} (f : V ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (h : Set.range f.base ∩ Set.range j.base = ∅) :
    IsEmpty ↥(Limits.pullback f j) := by
  have hr : Set.range (Limits.pullback.fst f j).base = ∅ := by
    rw [IsOpenImmersion.range_pullbackFst]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hmem : f.base x ∈ Set.range f.base ∩ Set.range j.base := ⟨⟨x, rfl⟩, hx⟩
    rw [h] at hmem
    exact hmem
  exact Set.range_eq_empty_iff.mp hr

end DisjointRange

end AlgebraicGeometry
