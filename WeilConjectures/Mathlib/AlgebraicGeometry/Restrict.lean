/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.Mathlib.Data.Set.Image

/-!
# Restrictions of morphisms of schemes along open immersions

We record:

- `AlgebraicGeometry.morphismRestrictArrowIso` — transport of a morphism restriction along
  compatible open immersions;
- `AlgebraicGeometry.mem_opensRange_homOfLE` / `AlgebraicGeometry.homOfLE_preimage_opensRange`
  — membership and preimage formulas for the ranges of inclusions of opens;
- the **lift of an open immersion along a partial isomorphism**: if `π : T ⟶ X` is an
  isomorphism over the range of an open immersion `j : Z ⟶ X`, then `j` lifts through `π`
  (`AlgebraicGeometry.liftOfIsIsoRestrict`, built from
  `AlgebraicGeometry.isoPreimageOpensRange`), and the resulting triangle is cartesian
  (`AlgebraicGeometry.isPullback_liftOfIsIsoRestrict`). Everything else in the section is read
  off that square: the lift is unique (`AlgebraicGeometry.eq_liftOfIsIsoRestrict`), hence any
  morphism over `j` is an open immersion
  (`AlgebraicGeometry.isOpenImmersion_of_comp_eq`) with range the full inverse image of the
  range of `j` (`AlgebraicGeometry.range_eq_preimage_range_of_comp_eq` and
  `AlgebraicGeometry.opensRange_eq_preimage_opensRange_of_comp_eq`), and it computes images as
  inverse images (`AlgebraicGeometry.image_eq_preimage_image_of_comp_eq`).
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

/-- A morphism which is an isomorphism over an open `W` is an isomorphism over the range of
the inclusion of `W`. -/
instance isIso_morphismRestrict_opensRange_ι (W : X.Opens) [IsIso (π ∣_ W)] :
    IsIso (π ∣_ W.ι.opensRange) := by
  rw [Scheme.Opens.opensRange_ι]
  infer_instance

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
        liftOfIsIsoRestrict π j
   Z ───────────────────────────→ T
    ╲                             │
   j ╲                            │ π
      ↘                           ↓
                                  X
```
-/
def liftOfIsIsoRestrict : Z ⟶ T :=
  (isoPreimageOpensRange π j).hom ≫ (π ⁻¹ᵁ j.opensRange).ι

instance isOpenImmersion_liftOfIsIsoRestrict : IsOpenImmersion (liftOfIsIsoRestrict π j) := by
  delta liftOfIsIsoRestrict
  infer_instance

@[reassoc (attr := simp)]
lemma liftOfIsIsoRestrict_comp : liftOfIsIsoRestrict π j ≫ π = j := by
  rw [liftOfIsIsoRestrict, isoPreimageOpensRange, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    Scheme.Hom.isoOpensRange_hom_ι]

/-- The lift of an open immersion along a partial isomorphism has as range the full inverse
image of the range of the open immersion. -/
@[simp]
lemma opensRange_liftOfIsIsoRestrict :
    (liftOfIsIsoRestrict π j).opensRange = π ⁻¹ᵁ j.opensRange := by
  have hsurj : Function.Surjective ⇑(isoPreimageOpensRange π j).hom :=
    (Scheme.homeoOfIso (isoPreimageOpensRange π j)).surjective
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, liftOfIsIsoRestrict, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hsurj.range_eq, Set.image_univ, Scheme.Opens.range_ι]

/-- **The lift of an open immersion along a partial isomorphism is cartesian**: the triangle

```
        liftOfIsIsoRestrict π j
   Z ───────────────────────────→ T
    ╲                             │
   j ╲                            │ π
      ↘                           ↓
                                  X
```

exhibits `Z` as the fibre product of `j` and `π`, since the lift is an open immersion whose
range is the full inverse image of the range of `j`. -/
theorem isPullback_liftOfIsIsoRestrict :
    IsPullback (𝟙 Z) (liftOfIsIsoRestrict π j) j π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [liftOfIsIsoRestrict_comp, Category.id_comp])
    (opensRange_liftOfIsIsoRestrict π j).symm

end

variable (q : Z ⟶ T) {j : Z ⟶ X} [IsOpenImmersion j] [IsIso (π ∣_ j.opensRange)]

/-- **Uniqueness of the lift of an open immersion along a partial isomorphism**: any `q` with
`q ≫ π = j` is the lift `liftOfIsIsoRestrict π j`.

```
        q
   Z ───────→ T
    ╲         │
   j ╲        │ π       q ≫ π = j, with π an isomorphism over the range of j
      ↘       ↓
              X
```
-/
theorem eq_liftOfIsIsoRestrict (hq : q ≫ π = j) : q = liftOfIsIsoRestrict π j :=
  (isPullback_liftOfIsIsoRestrict π j).eq_of_comp_eq hq

/-- **A lift of an open immersion along a partial isomorphism is an open immersion**: if
`q ≫ π = j` with `j` an open immersion and `π` an isomorphism over the range of `j`, then `q`
is an open immersion, being the unique lift `liftOfIsIsoRestrict π j` (see
`AlgebraicGeometry.eq_liftOfIsIsoRestrict` for the triangle). -/
theorem isOpenImmersion_of_comp_eq (hq : q ≫ π = j) : IsOpenImmersion q := by
  rw [eq_liftOfIsIsoRestrict π q hq]
  infer_instance

/-- **The range of a lift of an open immersion along a partial isomorphism** is the full inverse
image of the range of the open immersion (see `AlgebraicGeometry.eq_liftOfIsIsoRestrict` for the
triangle). -/
theorem range_eq_preimage_range_of_comp_eq (hq : q ≫ π = j) :
    Set.range q = π ⁻¹' Set.range j := by
  rw [eq_liftOfIsIsoRestrict π q hq, ← Scheme.Hom.coe_opensRange,
    opensRange_liftOfIsIsoRestrict]
  simp

/-- **The range of a lift of an open immersion along a partial isomorphism** is the full inverse
image of the range of the open immersion, as opens (see
`AlgebraicGeometry.eq_liftOfIsIsoRestrict` for the triangle). -/
theorem opensRange_eq_preimage_opensRange_of_comp_eq [IsOpenImmersion q] (hq : q ≫ π = j) :
    q.opensRange = π ⁻¹ᵁ j.opensRange :=
  TopologicalSpace.Opens.ext (by simpa using range_eq_preimage_range_of_comp_eq π q hq)

/-- **A lift of an open immersion along a partial isomorphism computes images as preimages**:
the image under `q` of a subset of `Z` is the full inverse image under `π` of its image
under `j` (see `AlgebraicGeometry.eq_liftOfIsIsoRestrict` for the triangle). -/
theorem image_eq_preimage_image_of_comp_eq (hq : q ≫ π = j) (A : Set Z) :
    q '' A = π ⁻¹' (j '' A) :=
  Set.image_eq_preimage_image (fun z ↦ by rw [← Scheme.Hom.comp_apply, hq])
    j.isOpenEmbedding.injective (range_eq_preimage_range_of_comp_eq π q hq) A

end LiftAlongPartialIso

end AlgebraicGeometry
