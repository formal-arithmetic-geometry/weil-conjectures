/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restrictions of morphisms of schemes along open immersions

We record:

- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions;
- `AlgebraicGeometry.mem_opensRange_homOfLE` / `AlgebraicGeometry.homOfLE_preimage_opensRange`
  — membership and preimage formulas for the ranges of inclusions of opens;
- the **lift of an open immersion along a partial isomorphism**
  `AlgebraicGeometry.liftOfIsIsoRestrict`: if `π : T ⟶ X` is an isomorphism over the range of
  an open immersion `j : Z ⟶ X`, then `j` lifts to an open immersion `Z ⟶ T` onto the inverse
  image of the range of `j`, and any lift of `j` along `π` is this one
  (`AlgebraicGeometry.eq_liftOfIsIsoRestrict`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y Z Z' : Scheme.{u}}

/-- If `e ≫ f = q ≫ j` with `e`, `j` open immersions and `f ⁻¹ᵁ (range j) = range e`, then
the restriction `f ∣_ j.opensRange` is isomorphic to `q` in the arrow category. -/
noncomputable def morphismRestrictArrowIso (f : X ⟶ Y) {e : Z ⟶ X} {j : Z' ⟶ Y}
    (q : Z ⟶ Z') [IsOpenImmersion e] [IsOpenImmersion j]
    (w : e ≫ f = q ≫ j) (h : f ⁻¹ᵁ j.opensRange = e.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk q := by
  have hα : Set.range ⇑(f ⁻¹ᵁ j.opensRange).ι = Set.range ⇑e := by
    rw [Scheme.Opens.range_ι, h]; rfl
  have hβ : Set.range ⇑j.opensRange.ι = Set.range ⇑j := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) q
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι e hα)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hβ) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← w,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

/-- Membership in the range of the inclusion of a smaller open. -/
lemma mem_opensRange_homOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V)
    (x : V.toScheme) : x ∈ (X.homOfLE hUV).opensRange ↔ x.1 ∈ U := by
  rw [Scheme.opensRange_homOfLE]
  exact Iff.rfl

/-- Preimages of ranges of inclusions of opens. -/
lemma homOfLE_preimage_opensRange {X : Scheme.{u}} {U V W : X.Opens} (hWU : W ≤ U)
    (hUV : U ≤ V) :
    X.homOfLE hUV ⁻¹ᵁ (X.homOfLE (hWU.trans hUV)).opensRange =
      (X.homOfLE hWU).opensRange := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.homOfLE_ι]

section LiftAlongPartialIso

variable {T : Scheme.{u}} (π : T ⟶ X)

section

variable (j : Z ⟶ X) [IsOpenImmersion j] [IsIso (π ∣_ j.opensRange)]

/-- If `π : T ⟶ X` is an isomorphism over the range of an open immersion `j : Z ⟶ X`, then `Z`
is isomorphic to the inverse image in `T` of the range of `j`. -/
def isoPreimageOpensRange : Z ≅ (π ⁻¹ᵁ j.opensRange).toScheme :=
  j.isoOpensRange ≪≫ (asIso (π ∣_ j.opensRange)).symm

/-- **The lift of an open immersion along a partial isomorphism**: if `π : T ⟶ X` is an
isomorphism over the range of an open immersion `j : Z ⟶ X`, then `j` lifts through `π` to the
inverse image of the range of `j`.

```
        q
   Z ───────→ T
    ╲         │
   j ╲        │ π       q ≫ π = j, with π an isomorphism over the range of j
      ↘       ↓
              X
```
-/
def liftOfIsIsoRestrict : Z ⟶ T :=
  (isoPreimageOpensRange π j).hom ≫ (π ⁻¹ᵁ j.opensRange).ι

instance : IsOpenImmersion (liftOfIsIsoRestrict π j) := by
  rw [liftOfIsIsoRestrict]
  infer_instance

@[reassoc (attr := simp)]
lemma liftOfIsIsoRestrict_comp : liftOfIsIsoRestrict π j ≫ π = j := by
  rw [liftOfIsIsoRestrict, isoPreimageOpensRange, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    Scheme.Hom.isoOpensRange_hom_ι]

end

variable (q : Z ⟶ T) {j : Z ⟶ X} [IsOpenImmersion j] [IsIso (π ∣_ j.opensRange)]

/-- **Uniqueness of the lift of an open immersion along a partial isomorphism**: any `q` with
`q ≫ π = j` is the lift `liftOfIsIsoRestrict π j`. -/
theorem eq_liftOfIsIsoRestrict (hq : q ≫ π = j) : q = liftOfIsIsoRestrict π j := by
  have hqπ (z : Z) : π (q z) = j z := by rw [← Scheme.Hom.comp_apply, hq]
  have hrange : Set.range q ⊆ ((π ⁻¹ᵁ j.opensRange : T.Opens) : Set T) := by
    rintro - ⟨z, rfl⟩
    exact ⟨z, (hqπ z).symm⟩
  set q' : Z ⟶ (π ⁻¹ᵁ j.opensRange).toScheme :=
    IsOpenImmersion.lift (π ⁻¹ᵁ j.opensRange).ι q (by rwa [Scheme.Opens.range_ι])
  have hq' : q' ≫ (π ⁻¹ᵁ j.opensRange).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hfac : q' ≫ (π ∣_ j.opensRange) = j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hq',
      hq, Scheme.Hom.isoOpensRange_hom_ι]
  have hiso : q' = (isoPreimageOpensRange π j).hom := by
    rw [isoPreimageOpensRange, Iso.trans_hom, Iso.symm_hom, asIso_inv, ← hfac, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [← hq', hiso, liftOfIsIsoRestrict]

/-- **A lift of an open immersion along a partial isomorphism is an open immersion**: if
`q ≫ π = j` with `j` an open immersion and `π` an isomorphism over the range of `j`, then `q`
is an open immersion. -/
theorem isOpenImmersion_of_comp_eq (hq : q ≫ π = j) : IsOpenImmersion q := by
  rw [eq_liftOfIsIsoRestrict π q hq]
  infer_instance

/-- **The range of a lift of an open immersion along a partial isomorphism** is the full inverse
image of the range of the open immersion. -/
theorem range_eq_preimage_range_of_comp_eq (hq : q ≫ π = j) :
    Set.range q = π ⁻¹' Set.range j := by
  have hcoe : ⇑((isoPreimageOpensRange π j).hom ≫ (π ⁻¹ᵁ j.opensRange).ι) =
      ⇑(π ⁻¹ᵁ j.opensRange).ι ∘ ⇑(isoPreimageOpensRange π j).hom :=
    funext fun z ↦ Scheme.Hom.comp_apply _ _ _
  have hsurj : Function.Surjective ⇑(isoPreimageOpensRange π j).hom :=
    (Scheme.homeoOfIso (isoPreimageOpensRange π j)).surjective
  rw [eq_liftOfIsIsoRestrict π q hq, liftOfIsIsoRestrict, hcoe, hsurj.range_comp,
    Scheme.Opens.range_ι]
  simp

/-- **The range of a lift of an open immersion along a partial isomorphism** is the full inverse
image of the range of the open immersion, as opens. -/
theorem opensRange_eq_preimage_of_comp_eq [IsOpenImmersion q] (hq : q ≫ π = j) :
    q.opensRange = π ⁻¹ᵁ j.opensRange :=
  TopologicalSpace.Opens.ext (by simpa using range_eq_preimage_range_of_comp_eq π q hq)

/-- **A lift of an open immersion along a partial isomorphism computes images as preimages**:
the image under `q` of a subset of `Z` is the full inverse image under `π` of its image
under `j`. -/
theorem image_eq_preimage_image_of_comp_eq (hq : q ≫ π = j) (A : Set Z) :
    q '' A = π ⁻¹' (j '' A) := by
  have hqπ (z : Z) : π (q z) = j z := by rw [← Scheme.Hom.comp_apply, hq]
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hqπ z).symm⟩
  · rintro ⟨z, hz, hx⟩
    obtain ⟨z', rfl⟩ : x ∈ Set.range q := by
      rw [range_eq_preimage_range_of_comp_eq π q hq]
      exact ⟨z, hx⟩
    exact ⟨z', j.isOpenEmbedding.injective (hx.trans (hqπ z')) ▸ hz, rfl⟩

end LiftAlongPartialIso

end AlgebraicGeometry
