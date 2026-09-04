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
- `AlgebraicGeometry.image_preimage_morphismRestrict` — the restriction of a morphism to an
  open of the target computes preimages of subsets of that open;
- the **lifts of an open immersion along a partial isomorphism**
  `AlgebraicGeometry.isoPreimageOpensRange`, `AlgebraicGeometry.opensRange_eq_preimage_of_comp_eq`
  and `AlgebraicGeometry.isOpenImmersion_of_comp_eq`: if `q ≫ π` is an open immersion `j` and `π`
  is an isomorphism over the range of `j`, then `q` is an isomorphism onto the inverse image of
  the range of `j`.
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

/-- Restricting a morphism to an open `U` of the target computes preimages of subsets of `U`:
the image in `X` of the `f ∣_ U`-preimage of `T ⊆ U` is the `f`-preimage of the image of `T`. -/
lemma image_preimage_morphismRestrict (f : X ⟶ Y) (U : Y.Opens) (T : Set U.toScheme) :
    (f ⁻¹ᵁ U).ι '' ((f ∣_ U) ⁻¹' T) = f ⁻¹' (U.ι '' T) := by
  have hpre : (f ∣_ U) ⁻¹' T = (f ⁻¹ᵁ U).ι ⁻¹' (f ⁻¹' (U.ι '' T)) := by
    ext y
    have h : f ((f ⁻¹ᵁ U).ι y) = U.ι ((f ∣_ U) y) := by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
    simp only [Set.mem_preimage, h]
    exact U.ι.isOpenEmbedding.injective.mem_set_image.symm
  rw [hpre, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_eq_left]
  rintro x ⟨t, -, ht⟩
  change f x ∈ U
  rw [← ht]
  exact t.2

section LiftAlongPartialIso

/-- If `π : T ⟶ X` is an isomorphism over the range of an open immersion `j : Z ⟶ X`, then `Z`
is isomorphic to the inverse image in `T` of the range of `j`. -/
def isoPreimageOpensRange {T : Scheme.{u}} (π : T ⟶ X) (j : Z ⟶ X) [IsOpenImmersion j]
    [IsIso (π ∣_ j.opensRange)] : Z ≅ (π ⁻¹ᵁ j.opensRange).toScheme :=
  j.isoOpensRange ≪≫ (asIso (π ∣_ j.opensRange)).symm

variable {T : Scheme.{u}} (q : Z ⟶ T) (π : T ⟶ X) {j : Z ⟶ X} [IsOpenImmersion j]
  [IsIso (π ∣_ j.opensRange)]

/-- **A lift of an open immersion along a partial isomorphism is an isomorphism onto the
inverse image of the range**: if `q ≫ π = j` with `j` an open immersion and `π` an isomorphism
over the range of `j`, then `q` is `isoPreimageOpensRange π j` followed by the inclusion of
`π ⁻¹ᵁ j.opensRange`.

```
        q
   Z ───────→ T
    ╲         │
   j ╲        │ π       q ≫ π = j, with π an isomorphism over the range of j
      ↘       ↓
              X
```
-/
theorem eq_isoPreimageOpensRange_hom_comp_ι (hq : q ≫ π = j) :
    q = (isoPreimageOpensRange π j).hom ≫ (π ⁻¹ᵁ j.opensRange).ι := by
  have hrange : Set.range q ⊆ ((π ⁻¹ᵁ j.opensRange : T.Opens) : Set T) := by
    rintro - ⟨z, rfl⟩
    change π (q z) ∈ j.opensRange
    rw [show π (q z) = j z by rw [← Scheme.Hom.comp_apply, hq]]
    exact ⟨z, rfl⟩
  set q' : Z ⟶ (π ⁻¹ᵁ j.opensRange).toScheme :=
    IsOpenImmersion.lift (π ⁻¹ᵁ j.opensRange).ι q (by rwa [Scheme.Opens.range_ι]) with hq'def
  have hq' : q' ≫ (π ⁻¹ᵁ j.opensRange).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hfac : q' ≫ (π ∣_ j.opensRange) = j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hq',
      hq, Scheme.Hom.isoOpensRange_hom_ι]
  have hiso : q' = (isoPreimageOpensRange π j).hom := by
    rw [isoPreimageOpensRange, Iso.trans_hom, Iso.symm_hom, asIso_inv, ← hfac, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [← hq', hiso]

/-- **A lift of an open immersion along a partial isomorphism is an open immersion**: if
`q ≫ π = j` with `j` an open immersion and `π` an isomorphism over the range of `j`, then `q`
is an open immersion. -/
theorem isOpenImmersion_of_comp_eq (hq : q ≫ π = j) : IsOpenImmersion q := by
  rw [eq_isoPreimageOpensRange_hom_comp_ι q π hq]
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
  rw [eq_isoPreimageOpensRange_hom_comp_ι q π hq, hcoe, hsurj.range_comp,
    Scheme.Opens.range_ι]
  simp

/-- **The range of a lift of an open immersion along a partial isomorphism** is the full inverse
image of the range of the open immersion, as opens. -/
theorem opensRange_eq_preimage_of_comp_eq [IsOpenImmersion q] (hq : q ≫ π = j) :
    q.opensRange = π ⁻¹ᵁ j.opensRange :=
  TopologicalSpace.Opens.ext (by simpa using range_eq_preimage_range_of_comp_eq q π hq)

end LiftAlongPartialIso

end AlgebraicGeometry
