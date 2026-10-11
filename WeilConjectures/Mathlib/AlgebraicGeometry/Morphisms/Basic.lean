/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Properties local at the source or the target, checked on open immersions

A property `P` of morphisms which is local at the source holds for `f : X ⟶ Y` as soon as every
point of `X` lies in the image of an open immersion `g : U ⟶ X` with `P (g ≫ f)`. Dually, a
property local at the target holds for `f` as soon as every point of `Y` lies in the image of an
open immersion along which some base change of `f` has the property.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsZariskiLocalAtSource

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P] {X Y : Scheme.{u}}

/-- A property local at the source holds for `f : X ⟶ Y` if every point of `X` lies in the image
of an open immersion `g : U ⟶ X` such that `g ≫ f` has the property. -/
lemma of_forall_exists_isOpenImmersion (f : X ⟶ Y)
    (H : ∀ x : X, ∃ (U : Scheme.{u}) (g : U ⟶ X), IsOpenImmersion g ∧ x ∈ Set.range g.base ∧
      P (g ≫ f)) : P f := by
  choose U g hg hx hP using H
  refine of_iSup_eq_top (fun x ↦ (g x).opensRange) ?_ fun x ↦ ?_
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, ?_⟩
    simpa using hx x
  · have := hg x
    rw [← (g x).isoOpensRange_inv_comp, Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := P)]
    exact hP x

end AlgebraicGeometry.IsZariskiLocalAtSource

namespace AlgebraicGeometry.IsZariskiLocalAtTarget

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] {X Y : Scheme.{u}}

/-- A property local at the target holds for `f : X ⟶ Y` if every point of `Y` lies in the image
of an open immersion `j : V ⟶ Y` along which some base change `f' : U ⟶ V` of `f` has the
property. -/
lemma of_forall_exists_isPullback (f : X ⟶ Y)
    (H : ∀ y : Y, ∃ (U V : Scheme.{u}) (i : U ⟶ X) (f' : U ⟶ V) (j : V ⟶ Y),
      IsOpenImmersion j ∧ y ∈ Set.range j ∧ IsPullback i f' f j ∧ P f') : P f := by
  choose U V i f' j hj hy hpb hP using H
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y V j (fun y ↦ ⟨y, hy y⟩) hj
  refine of_openCover 𝒰 fun y ↦ ?_
  refine (P.arrow_mk_iso_iff (Arrow.isoMk (hpb y).isoPullback (Iso.refl _) ?_)).mp (hP y)
  simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id]
  exact (hpb y).isoPullback_hom_snd

end AlgebraicGeometry.IsZariskiLocalAtTarget
