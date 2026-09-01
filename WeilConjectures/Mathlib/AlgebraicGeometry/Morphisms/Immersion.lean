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

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Immersions respect open immersions on the right

The composition of an immersion with an open immersion is an immersion, stated as a
`MorphismProperty.RespectsRight` instance so that generic locality lemmas
(e.g. `IsZariskiLocalAtTarget.of_forall_source_exists_preimage`) apply to `IsImmersion`.

# Shrinking an immersion to a closed immersion

`AlgebraicGeometry.Scheme.Hom.exists_isCompact_isClosedImmersion`: an immersion `f : X ⟶ Y`
with `X` quasi-compact is a closed immersion into a quasi-compact open of `Y`. This is the
shrinking step of [Stacks, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG); note that no
quasi-separatedness assumption on `Y` is needed.
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

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp i hi f hf := by
    have : IsOpenImmersion i := hi
    have : IsImmersion f := hf
    infer_instance

variable {X Y : Scheme.{u}}

/-- **Shrinking an immersion to a closed immersion.** An immersion `f : X ⟶ Y` with `X`
quasi-compact factors as a closed immersion `g : X ⟶ W` into a quasi-compact open `W` of `Y`,
followed by the inclusion of `W`.

This is the shrinking step of [Stacks, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG);
no quasi-separatedness assumption on `Y` is needed. -/
@[stacks 01ZG]
theorem Scheme.Hom.exists_isCompact_isClosedImmersion (f : X ⟶ Y) [IsImmersion f]
    [CompactSpace X] :
    ∃ (W : Y.Opens) (g : X ⟶ W.toScheme), IsCompact (W : Set Y) ∧ IsClosedImmersion g ∧
      g ≫ W.ι = f := by
  classical
  have hsub : Set.range f.base ⊆ (f.coborderRange : Set Y) := subset_coborder
  have H : ∀ x : X, ∃ A : Y.affineOpens, f x ∈ A.1 ∧ A.1 ≤ f.coborderRange := by
    intro x
    obtain ⟨A, hA, hxA, hle⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show f x ∈ f.coborderRange from hsub ⟨x, rfl⟩)
    exact ⟨⟨A, hA⟩, hxA, hle⟩
  choose A hxA hAle using H
  obtain ⟨t, ht⟩ := (isCompact_range f.continuous).elim_finite_subcover
    (fun x : X ↦ (A x).1.1) (fun x ↦ (A x).1.2)
    (by rintro _ ⟨x, rfl⟩; exact Set.mem_iUnion.2 ⟨x, hxA x⟩)
  set W : Y.Opens := ⨆ x ∈ t, (A x).1 with hW
  have hWc : IsCompact (W : Set Y) := by
    have : (W : Set Y) = ⋃ x ∈ (t : Set X), ((A x).1 : Set Y) := by simp [hW]
    rw [this]
    exact t.finite_toSet.isCompact_biUnion fun x _ ↦ (A x).2.isCompact
  have hWle : W ≤ f.coborderRange := iSup₂_le fun x _ ↦ hAle x
  have hrange : Set.range f.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    simpa [hW] using ht
  refine ⟨W, IsOpenImmersion.lift W.ι f hrange, hWc, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have key : IsOpenImmersion.lift W.ι f hrange ≫ Y.homOfLE hWle = f.liftCoborder := by
    rw [← cancel_mono f.coborderRange.ι]
    simp
  have : IsClosedImmersion (IsOpenImmersion.lift W.ι f hrange ≫ Y.homOfLE hWle) := by
    rw [key]; infer_instance
  exact IsClosedImmersion.of_comp _ (Y.homOfLE hWle)

end AlgebraicGeometry
