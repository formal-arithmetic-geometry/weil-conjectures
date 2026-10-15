/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.CategoryTheory.SpectralObjectPageTwoMap

/-! # Functorial page-two realization of spectral objects

Source: the spectral-object kernel/image construction in Mathlib and Stacks Project,
Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-functor).
-/

@[expose] public section

universe uA vA uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

/-- The page-two spectral sequence construction is functorial in a family of spectral
objects, and the canonical computation of its first page is natural.
Source: Mathlib's spectral-object construction, and Stacks Project, Tags 012K and 015K
(blueprint: lem-sp-spectral-object-page-two-functor).

Proof: for each morphism of spectral objects, apply its cohomology components to the
three-term complexes defining the four-index page objects. Compatibility with the
connecting maps gives a morphism of these short complexes. Restrict to their kernels
and pass to the images of the maps from cycles to opcycles. This defines the map on each
page. Naturality of the connecting maps makes these maps commute with the page
differentials. The kernel/cokernel universal properties in the page homology computation
make them commute with the successor-page isomorphisms. The same universal properties
prove the identity and composition laws. Thus the resulting maps define E, whose objects
are the existing spectral sequences, with identity object comparisons c. At page two the
outer repeated indices make the page object the cohomology of a single interval; the
kernel and cokernel maps in that identification commute with the original cohomology
components. This is exactly the displayed naturality equation. No boundedness or
first-quadrant assumption enters these finite kernel/image computations. -/
theorem exists_pageTwo_functor
    {A : Type uA} [Category.{vA} A]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (S : A ⥤ SpectralObject C EInt) :
    ∃ (E : A ⥤ E₂CohomologicalSpectralSequence C)
      (c : ∀ X : A, E.obj X ≅ (S.obj X).E₂SpectralSequence),
      ∀ (X Y : A) (f : X ⟶ Y) (p q : ℤ),
        ((E.map f).hom 2).f (p, q) ≫
            (pageTwoComparison (S.obj Y) (c Y) p q (p + q) rfl).hom =
          (pageTwoComparison (S.obj X) (c X) p q (p + q) rfl).hom ≫
            ((S.map f).hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  classical
  let obj : A → E₂CohomologicalSpectralSequence C :=
    fun X => (S.obj X).E₂SpectralSequence
  let map := fun {X Y : A} (f : X ⟶ Y) =>
    Classical.choose (exists_unique_pageTwoMap (S.map f))
  have map_spec : ∀ {X Y : A} (f : X ⟶ Y),
      (∀ (p q : ℤ),
        ((map f).hom 2).f (p, q) ≫
            (pageTwoComparison (S.obj Y) (Iso.refl _) p q (p + q) rfl).hom =
          (pageTwoComparison (S.obj X) (Iso.refl _) p q (p + q) rfl).hom ≫
            ((S.map f).hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) :=
    fun {X Y} f => (Classical.choose_spec (exists_unique_pageTwoMap (S.map f))).1
  let E : A ⥤ E₂CohomologicalSpectralSequence C := {
    obj := obj
    map := @map
    map_id := by
      intro X
      symm
      apply (Classical.choose_spec (exists_unique_pageTwoMap (S.map (𝟙 X)))).2
      intro p q
      simp only [SpectralSequence.id_hom, Functor.map_id,
        Abelian.SpectralObject.id_hom]
      change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
      simp
    map_comp := by
      intro X Y Z f g
      symm
      apply (Classical.choose_spec (exists_unique_pageTwoMap (S.map (f ≫ g)))).2
      intro p q
      have hf := map_spec f p q
      have hg := map_spec g p q
      dsimp at hf hg ⊢
      rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
      have hfg := congrArg (fun k =>
        (k.hom (p + q)).app (ComposableArrows.mk₁
          (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) (S.map_comp f g)
      exact congrArg (fun t =>
        (pageTwoComparison (S.obj X) (Iso.refl _) p q (p + q) rfl).hom ≫ t)
        (by simpa only [Abelian.SpectralObject.comp_hom, NatTrans.comp_app] using hfg.symm)
  }
  refine ⟨E, fun X => Iso.refl _, ?_⟩
  intro X Y f p q
  exact map_spec f p q

end CategoryTheory.Abelian.SpectralObject
