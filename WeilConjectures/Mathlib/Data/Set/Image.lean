/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Set.Image

/-!
# Images under a lift along an injection

`Set.image_eq_preimage_image`: if `q : Z → T` lies over an injection `j : Z → X` via
`π : T → X` and its range is the full preimage of the range of `j`, then `q` computes images
as preimages: `q '' A = π ⁻¹' (j '' A)`.
-/

@[expose] public section

namespace Set

variable {Z T X : Type*} {q : Z → T} {π : T → X} {j : Z → X}

/-- If `π ∘ q = j` with `j` injective and the range of `q` the full preimage under `π` of the
range of `j`, then the image under `q` of a set is the full preimage under `π` of its image
under `j`. -/
theorem image_eq_preimage_image (hcomp : ∀ z, π (q z) = j z) (hj : Function.Injective j)
    (hrange : range q = π ⁻¹' range j) (A : Set Z) : q '' A = π ⁻¹' (j '' A) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hcomp z).symm⟩
  · rintro ⟨z, hz, hx⟩
    obtain ⟨z', rfl⟩ : x ∈ range q := hrange ▸ ⟨z, hx⟩
    obtain rfl := hj (hx.trans (hcomp z'))
    exact ⟨z, hz, rfl⟩

end Set
