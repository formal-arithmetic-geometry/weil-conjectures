/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Functorial page-two realization of spectral objects

Source: the spectral-object kernel/image construction in Mathlib and Stacks Project,
Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-functor).
-/

@[expose] public section

universe uA vA uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

/-- Evaluate a spectral-sequence comparison on page two and then use the canonical
first-page computation. This is an actual composite of existing isomorphisms.
Source: Mathlib's `spectralSequenceFirstPageXIso`
(blueprint: lem-sp-spectral-object-page-two-functor). -/
noncomputable def pageTwoComparison
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (Y : SpectralObject C EInt) {E : E₂CohomologicalSpectralSequence C}
    (c : E ≅ Y.E₂SpectralSequence) (p q n : ℤ) (hn : n = p + q) :
    (E.page 2).X (p, q) ≅
      (Y.H n).obj (ComposableArrows.mk₁
        (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) :=
  (HomologicalComplex.eval C _ (p, q)).mapIso
      ((SpectralSequence.pageFunctor C _ 2 2).mapIso c) ≪≫
    Y.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl n hn

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
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by sorry

end CategoryTheory.Abelian.SpectralObject
