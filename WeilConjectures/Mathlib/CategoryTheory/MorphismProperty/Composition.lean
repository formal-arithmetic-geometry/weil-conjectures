/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# The two-out-of-three property for an intersection of morphism properties

The instance `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.iInf` shows that an
indexed intersection `⨅ i, W i` of morphism properties which all have the two-out-of-three
property again has it.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

/-- An indexed intersection of morphism properties which have the two-out-of-three property
has the two-out-of-three property. -/
instance HasTwoOutOfThreeProperty.iInf {ι : Type*} {W : ι → MorphismProperty C}
    [∀ i, (W i).HasTwoOutOfThreeProperty] : (⨅ i, W i).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := by
    rw [iInf_iff] at hg hfg ⊢
    exact fun i ↦ (W i).of_postcomp f g (hg i) (hfg i)
  of_precomp f g hf hfg := by
    rw [iInf_iff] at hf hfg ⊢
    exact fun i ↦ (W i).of_precomp f g (hf i) (hfg i)

end CategoryTheory.MorphismProperty
