/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The inclusion of the Zariski site into the small étale site

The functor sending an open of a scheme `X` to the corresponding open subscheme, viewed as an
object of `X.Etale`, is cover preserving, preserves finite limits, and is continuous and
representably flat.

## References

* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 02GP](https://stacks.math.columbia.edu/tag/02GP)
* [Stacks Project, Tag 01JR](https://stacks.math.columbia.edu/tag/01JR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private noncomputable def openEtaleInclusion (X : Scheme.{u}) : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)

private def etaleImage (X : Scheme.{u}) : X.Etale ⥤ X.Opens where
  obj T := ⟨Set.range T.hom, T.hom.isOpenMap.isOpen_range⟩
  map {T S} f := homOfLE (by
    rintro x ⟨y, rfl⟩
    exact ⟨f.left y, congr($(CategoryTheory.Over.w f.hom) y)⟩)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etaleImageHomEquiv (X : Scheme.{u}) (T : X.Etale)
    (U : X.Opens) : ((etaleImage X).obj T ⟶ U) ≃ (T ⟶ (openEtaleInclusion X).obj U) where
  toFun h := MorphismProperty.Over.homMk
    (IsOpenImmersion.lift U.ι T.hom (by
      rintro y hy
      exact ⟨⟨y, h.le hy⟩, rfl⟩))
    (IsOpenImmersion.lift_fac _ _ _) trivial
  invFun f := homOfLE (by
    rintro x ⟨y, rfl⟩
    have h := congr($(CategoryTheory.Over.w f.hom) y)
    exact h ▸ (f.left y).property)
  left_inv _ := Subsingleton.elim _ _
  right_inv f := by
    apply (Scheme.Etale.forget X).map_injective
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    exact (IsOpenImmersion.lift_fac _ _ _).trans (CategoryTheory.Over.w f.hom).symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etaleImageAdjunction (X : Scheme.{u}) :
    etaleImage X ⊣ openEtaleInclusion X :=
  Adjunction.mkOfHomEquiv {
    homEquiv := etaleImageHomEquiv X
    homEquiv_naturality_left_symm := fun _ _ ↦ Subsingleton.elim _ _
    homEquiv_naturality_right := by
      intro T U V f g
      apply (Scheme.Etale.forget X).map_injective
      apply Over.OverMorphism.ext
      apply (cancel_mono V.ι).mp
      exact (CategoryTheory.Over.w _).trans (CategoryTheory.Over.w _).symm }

/-- Core site data for the Zariski-to-etale inclusion: there is a functor from opens of `X`
to `X.Etale` lifting `X.restrictFunctor` which is cover preserving, preserves finite limits,
sends `⊤` to a terminal object, and is continuous and representably flat. -/
theorem zariski_to_etale_core (X : Scheme.{u}) :
    ∃ (i : X.Opens ⥤ X.Etale),
      (i ⋙ Scheme.Etale.forget X = X.restrictFunctor) ∧
      CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i ∧
      PreservesFiniteLimits i ∧
      Nonempty (IsTerminal (i.obj ⊤)) ∧
      i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology ∧
        RepresentablyFlat i := by
  -- The open-image adjunction supplies the limit comparisons.
  let i := openEtaleInclusion X
  let : i.IsRightAdjoint := (etaleImageAdjunction X).isRightAdjoint
  let : PreservesFiniteLimits i := inferInstance
  let : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  have hcover : CoverPreserving (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology i := by
    constructor
    intro U S hS
    obtain ⟨J, V, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨W, g, hg, hx⟩ := hS x.val x.property
    obtain ⟨A, a, b, ⟨j⟩, hab⟩ := hg
    refine ⟨j, ⟨x.val, a.le hx⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply (f j).le _
  have hcont : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology := (Functor.isContinuous_iff_coverPreserving).2 hcover
  have hforget : i ⋙ Scheme.Etale.forget X = X.restrictFunctor := by
    rfl
  exact ⟨i, hforget, hcover, inferInstance,
    ⟨isTerminalTop.isTerminalObj i ⊤⟩, hcont, inferInstance⟩

end AlgebraicGeometry
