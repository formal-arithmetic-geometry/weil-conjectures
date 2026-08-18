/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Open immersions respect open immersions on the right

The `MorphismProperty.RespectsRight` instance for open immersions of schemes.

We also record the structure of **lifts of an open immersion along a partial
isomorphism**: if `q ≫ π` is an open immersion `j` and `π` is an isomorphism over the
range of `j`, then `q` factors as an isomorphism onto the full inverse image of the
range of `j`; in particular `q` is an open immersion
(`AlgebraicGeometry.isOpenImmersion_of_comp_of_isIso_restrict`) with range the inverse
image of the range of `j`
(`AlgebraicGeometry.range_eq_preimage_of_comp_of_isIso_restrict`). These describe the
embedded copies of preserved opens in admissible blow-ups.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

section LiftAlongPartialIso

variable {T X' X : Scheme.{u}} (q : T ⟶ X') (π : X' ⟶ X) (j : T ⟶ X) [IsOpenImmersion j]

/-- A lift `q` of an open immersion `j` along a morphism `π` which is an isomorphism
over the range of `j` factors as an isomorphism followed by the inclusion of the
inverse image of the range of `j`. -/
theorem eq_isoOpensRange_inv_restrict_comp_ι_of_comp (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) :
    q = (j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange)) ≫ (π ⁻¹ᵁ j.opensRange).ι := by
  have hrange : Set.range q ⊆ ((π ⁻¹ᵁ j.opensRange : X'.Opens) : Set X') := by
    rintro - ⟨t, rfl⟩
    change π (q t) ∈ j.opensRange
    have : π (q t) = j t := by
      rw [← Scheme.Hom.comp_apply, hq]
    rw [this]
    exact ⟨t, rfl⟩
  let q' : T ⟶ (π ⁻¹ᵁ j.opensRange).toScheme :=
    IsOpenImmersion.lift (π ⁻¹ᵁ j.opensRange).ι q (by rwa [Scheme.Opens.range_ι])
  have hq' : q' ≫ (π ⁻¹ᵁ j.opensRange).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hfac : q' ≫ (π ∣_ j.opensRange) = j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hq', hq, Scheme.Hom.isoOpensRange_hom_ι]
  have hq'iso : q' = j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange) := by
    rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← hq', hq'iso]

/-- **A lift of an open immersion along a partial isomorphism is an open immersion**:
if `q ≫ π = j` with `j` an open immersion and `π` an isomorphism over the range of
`j`, then `q` is an open immersion. -/
theorem isOpenImmersion_of_comp_of_isIso_restrict (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) : IsOpenImmersion q := by
  rw [eq_isoOpensRange_inv_restrict_comp_ι_of_comp q π j hq hiso]
  infer_instance

/-- **The range of a lift of an open immersion along a partial isomorphism** is the
full inverse image of the range of the open immersion. -/
theorem range_eq_preimage_of_comp_of_isIso_restrict (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) : Set.range q = π ⁻¹' (Set.range j) := by
  have hfac := eq_isoOpensRange_inv_restrict_comp_ι_of_comp q π j hq hiso
  apply subset_antisymm
  · rintro - ⟨t, rfl⟩
    refine Set.mem_preimage.mpr ⟨t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hq]
  · intro x' hx'
    have hx'P : x' ∈ Set.range (π ⁻¹ᵁ j.opensRange).ι := by
      rw [Scheme.Opens.range_ι]
      exact Set.mem_preimage.mp hx'
    obtain ⟨p, rfl⟩ := hx'P
    obtain ⟨t, ht⟩ := (Scheme.homeoOfIso
      (asIso (j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange)))).surjective p
    refine ⟨t, ?_⟩
    rw [hfac, Scheme.Hom.comp_apply]
    exact congrArg (π ⁻¹ᵁ j.opensRange).ι (by simpa using ht)

end LiftAlongPartialIso

end AlgebraicGeometry
