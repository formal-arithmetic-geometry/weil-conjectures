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
- `AlgebraicGeometry.isPullback_resLE_homOfLE` — the restriction of a morphism to a smaller open
  of the target is the base change of its restriction to a larger one.
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

open CategoryTheory.Limits in
/-- The restriction of `f : X ⟶ Y` to an open `W` of `Y` is the base change of its restriction
to a larger open `U`, provided that the chosen open `W'` of `X` is the intersection of `U'` with
the preimage of `W`. -/
lemma isPullback_resLE_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U W : Y.Opens} (h : W ≤ U)
    {U' W' : X.Opens} (h' : W' ≤ U') (e : U' ≤ f ⁻¹ᵁ U) (e' : W' ≤ f ⁻¹ᵁ W)
    (hpb : U' ⊓ f ⁻¹ᵁ W ≤ W') :
    IsPullback (f.resLE W W' e') (X.homOfLE h') (Y.homOfLE h) (f.resLE U U' e) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [← cancel_mono U.ι]
    simp [Scheme.Hom.resLE_comp_ι]
  · rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]
    refine le_antisymm (fun x hx ↦ hpb ⟨x.2, hx⟩) (fun x hx ↦ e' hx)

end AlgebraicGeometry
