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
- `AlgebraicGeometry.exists_opens_restrict_preimage` — a morphism defined on an open subscheme
  restricts to the open subscheme of points mapping into a given open of the target.
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

/-- **Restricting a morphism defined on an open subscheme to the preimage of an open of the
target.** For `F : W₁ ⟶ Z` with `W₁` an open subscheme of `X` and `V` an open of `Z`, the set
of points of `W₁` mapping into `V` is an open `W ≤ W₁` of `X`, and `F` restricts to a morphism
`W ⟶ V`. -/
lemma exists_opens_restrict_preimage {X Z : Scheme.{u}} (W₁ : X.Opens)
    (F : W₁.toScheme ⟶ Z) (V : Z.Opens) :
    ∃ (W : X.Opens) (hW : W ≤ W₁) (F' : W.toScheme ⟶ V.toScheme),
      F' ≫ V.ι = X.homOfLE hW ≫ F ∧ ∀ x : W₁.toScheme, x.1 ∈ W ↔ F x ∈ V := by
  have hle : W₁.ι ''ᵁ (F ⁻¹ᵁ V) ≤ W₁ := W₁.ι_image_le _
  have hsub : Set.range (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι.base ⊆
      Set.range ((F ⁻¹ᵁ V).ι ≫ W₁.ι).base := by
    simp [Scheme.Opens.range_ι, Set.range_comp]
  set e := IsOpenImmersion.lift ((F ⁻¹ᵁ V).ι ≫ W₁.ι) (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι hsub with he
  have hefac : e ≫ ((F ⁻¹ᵁ V).ι ≫ W₁.ι) = (W₁.ι ''ᵁ (F ⁻¹ᵁ V)).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hhom : X.homOfLE hle = e ≫ (F ⁻¹ᵁ V).ι := by
    rw [← cancel_mono W₁.ι, Scheme.homOfLE_ι, Category.assoc, hefac]
  refine ⟨W₁.ι ''ᵁ (F ⁻¹ᵁ V), hle, e ≫ (F ∣_ V), ?_, ?_⟩
  · rw [hhom, Category.assoc, Category.assoc, morphismRestrict_ι]
  · exact fun _ ↦ Scheme.Opens.mem_ι_image_iff W₁

end AlgebraicGeometry
