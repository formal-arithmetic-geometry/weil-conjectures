/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Complements on immersions

Two unrelated additions to Mathlib's `AlgebraicGeometry.IsImmersion`:

- `AlgebraicGeometry.IsImmersion.respectsRight_isOpenImmersion`: immersions are stable under
  post-composition with open immersions. This is the instance needed to apply
  `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup` to `IsImmersion`.
- `AlgebraicGeometry.isImmersion_left_pi_lift`: a tuple of morphisms of `S`-schemes one of
  whose components is an immersion is itself an immersion. Here the fibre product over `S` is
  the categorical product in `Over S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace IsImmersion

instance respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp _ hi _ hf := by
    have := hi
    have := hf
    infer_instance

end IsImmersion

variable {ι : Type*} {S : Scheme.{u}} (Y : ι → Over S) [HasProduct Y] (T : Over S)
  (g : ∀ i, T ⟶ Y i)

/-- **A tuple of morphisms of `S`-schemes one of whose components is an immersion is an
immersion**: if `gⱼ : T ⟶ Yⱼ` are morphisms over `S` and `g i` is an immersion, then
`(gⱼ)ⱼ : T ⟶ ∏_S Yⱼ` is an immersion, since composing it with the `i`-th projection gives back
`g i`.

Here the fibre product `∏_S Yⱼ` over `S` is the categorical product in `Over S`. -/
lemma isImmersion_left_pi_lift (i : ι) (h : IsImmersion (g i).left) :
    IsImmersion (Pi.lift g).left := by
  have : IsImmersion ((Pi.lift g).left ≫ (Pi.π Y i).left) := by
    rw [← Over.comp_left, Pi.lift_π]; infer_instance
  exact .of_comp _ (Pi.π Y i).left

end AlgebraicGeometry
