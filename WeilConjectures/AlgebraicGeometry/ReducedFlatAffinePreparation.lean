/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineReductionPreparation
import WeilConjectures.AlgebraicGeometry.AffinePreparationRestriction

/-! # Reduction and the first generic-flat shrinking

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
* [Stacks Project, Tag 052A](https://stacks.math.columbia.edu/tag/052A)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Prepare a reduced affine flat family over an integral affine base, before any
purely inseparable extension. -/
theorem exists_reduced_flat_affine_preparation
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ) (hηV : η ∈ V) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Z : Scheme.{u}) (q : S ⟶ U.toScheme)
        (h : Z ⟶ pullback f (q ≫ U.ι)),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Z ∧ IsReduced Z ∧
        IsUniversalHomeomorphism q ∧ IsUniversalHomeomorphism h ∧
        Flat (h ≫ pullback.snd f (q ≫ U.ι)) ∧
        LocallyOfFinitePresentation (h ≫ pullback.snd f (q ≫ U.ι)) ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η := by
  obtain ⟨S, Z, q, h, hSa, hSi, hZa, hZr, hq, hh, hft⟩ :=
    exists_affine_reduction_preparation f V hV himage η hη hηV
  let := hSa
  let := hSi
  let := hZa
  let := hZr
  let := hq
  let := hh
  let g := h ≫ pullback.snd f (q ≫ V.ι)
  let : LocallyOfFiniteType g := hft
  obtain ⟨W, hW, hflat, hfp⟩ := exists_nonempty_open_flat_finitePresentation_restrict g
  obtain ⟨η₀, he₀⟩ := q.surjective ⟨η, hηV⟩
  have hη₀ : IsGenericPoint η₀ Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro s
    simp only [Set.mem_univ, iff_true]
    apply q.isHomeomorph.isEmbedding.isInducing.specializes_iff.mp
    apply V.ι.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp
    have he : V.ι (q η₀) = η := congrArg Subtype.val he₀
    rw [he]
    exact hη.specializes (Set.mem_univ _)
  have hη₀W : η₀ ∈ W := (hη₀.mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have he₀T : (q ≫ V.ι) η₀ = η := congrArg Subtype.val he₀
  obtain ⟨U, hηU, hU, S', Z', q', h', hSa', hSi', hZa', hZr', hq', hh', hf', hp'⟩ :=
    exists_affine_preparation_restriction f V q h W hflat hfp η₀ hη₀W η he₀T
  let := hq'
  obtain ⟨η', he'⟩ := q'.surjective ⟨η, hηU⟩
  have hη' : IsGenericPoint η' Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro s
    simp only [Set.mem_univ, iff_true]
    apply q'.isHomeomorph.isEmbedding.isInducing.specializes_iff.mp
    apply U.ι.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp
    have he : U.ι (q' η') = η := congrArg Subtype.val he'
    rw [he]
    exact hη.specializes (Set.mem_univ _)
  exact ⟨U, hηU, hU, S', Z', q', h', hSa', hSi', hZa', hZr', hq', hh', hf', hp',
    η', hη', congrArg Subtype.val he'⟩

end AlgebraicGeometry
