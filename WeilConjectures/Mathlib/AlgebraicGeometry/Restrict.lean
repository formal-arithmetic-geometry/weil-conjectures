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
- `AlgebraicGeometry.Scheme.Hom.appIso_homOfLE_hom` — the sections isomorphism of an inclusion
  of opens is a restriction map.
-/

@[expose] public section

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

/-- An open `W ≤ U` is contained in the image of its preimage under `U.ι`. -/
lemma Scheme.Opens.le_ι_image_ι_preimage {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U) :
    W ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ W := by
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, h]

/-- The image in `X` of an open of `V` under `V ⟶ U ⟶ X` is its image under `V.ι`. -/
lemma Scheme.ι_image_homOfLE_image {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U)
    (P : (V : Scheme.{u}).Opens) : U.ι ''ᵁ X.homOfLE h ''ᵁ P = V.ι ''ᵁ P := by
  simp [← Scheme.Hom.comp_image]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism of sections `Γ(V, X.homOfLE h ''ᵁ W) ≅ Γ(U, W)` of the inclusion of opens
`U ≤ V` is a restriction map of `X`. -/
lemma Scheme.Hom.appIso_homOfLE_hom {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (W : (U : Scheme.{u}).Opens) :
    ((X.homOfLE h).appIso W).hom =
      X.presheaf.map (.op <| homOfLE <| by
        suffices U.ι ''ᵁ W ≤ V.ι ''ᵁ _ by simpa
        simp [← Scheme.Hom.comp_image]) := by
  apply (cancel_mono ((X.homOfLE h).appIso W).inv).1
  rw [Iso.hom_inv_id]
  erw [Scheme.Hom.appIso_homOfLE_inv, ← Functor.map_comp]
  exact (X.presheaf.map_id _).symm

end AlgebraicGeometry
