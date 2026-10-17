/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# Generic smoothness over a perfect field

Let `Y` be a scheme locally of finite type over a perfect field `E`. The smooth locus of the
reduction `Y_red ⟶ Spec E` is dense (`Scheme.Hom.dense_smoothLocus_of_perfectField`), so `Y`
has a dense open `W` whose reduction is smooth over `E`.

## Main statements

- `AlgebraicGeometry.exists_dense_isClosedImmersion_smooth_of_perfectField`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Generic smoothness over a perfect field.** Let `g : Y ⟶ Spec E` be locally of finite
type, `E` a perfect field. There are a dense open `W ⊆ Y` and a surjective closed immersion
`z : Z ⟶ W` with `Z` smooth over `E` (namely `Z = W_red`). -/
theorem exists_dense_isClosedImmersion_smooth_of_perfectField {E : Type u} [Field E]
    [PerfectField E] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of E)) [LocallyOfFiniteType g] :
    ∃ (W : Y.Opens) (Z : Scheme.{u}) (z : Z ⟶ W.toScheme),
      Dense (W : Set Y) ∧ IsClosedImmersion z ∧ Surjective z ∧ Smooth (z ≫ W.ι ≫ g) := by
  obtain ⟨hred, -, hsurj, -⟩ :=
    reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism Y
  have := hred
  set r := Y.nilradical.subschemeι
  have hr : IsHomeomorph r.base := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨r.isEmbedding, r.surjective⟩
  set O := (r ≫ g).smoothLocus
  have hO : Dense (O : Set Y.nilradical.subscheme) := (r ≫ g).dense_smoothLocus_of_perfectField
  let W : Y.Opens := ⟨r.base '' O, hr.isOpenMap _ O.isOpen⟩
  have hWO : r ⁻¹ᵁ W = O := by
    ext x
    exact hr.injective.mem_set_image
  refine ⟨W, O.toScheme, (Y.nilradical.subscheme.isoOfEq hWO).inv ≫ r ∣_ W, ?_, ?_, ?_, ?_⟩
  · exact hr.surjective.denseRange.dense_image hr.continuous hO
  · infer_instance
  · have : Surjective (r ∣_ W) := IsZariskiLocalAtTarget.restrict hsurj W
    infer_instance
  · rw [Category.assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    ext x
    simp

end AlgebraicGeometry
