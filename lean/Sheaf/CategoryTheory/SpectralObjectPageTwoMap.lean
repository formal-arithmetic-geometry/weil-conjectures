/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # The page-two map extension for spectral-object morphisms

Source: Mathlib's spectral-object kernel/image construction and Stacks Project,
Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-map-extension).
-/

@[expose] public section

universe uC vC

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


/-- A morphism of spectral objects induces a unique morphism of the canonical
`E₂` spectral sequences whose page-two map is the map transported by the
first-page comparison. The construction is by the finite kernel/image maps in
`SpectralSequence.pageX`; compatibility with the connecting maps proves the
page morphism equations, and induction through the successor-page homology
isomorphisms proves uniqueness. This is the local kernel/image step used to
construct the functorial page-two realization.
Source: Mathlib Algebra/Homology/SpectralObject/{Page,SpectralSequence,FirstPage}.lean,
Stacks Project Tags 012K and 015K.
(blueprint: lem-sp-spectral-object-page-two-map-extension).
-/
theorem exists_unique_pageTwoMap
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : SpectralObject C EInt} (φ : X ⟶ Y) :
    ∃ e : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
      (∀ (p q : ℤ),
        (e.hom 2).f (p, q) ≫
            (pageTwoComparison Y (Iso.refl _) p q (p + q) rfl).hom =
          (pageTwoComparison X (Iso.refl _) p q (p + q) rfl).hom ≫
            (φ.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) ∧
      ∀ e' : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
        (∀ (p q : ℤ),
          (e'.hom 2).f (p, q) ≫
              (pageTwoComparison Y (Iso.refl _) p q (p + q) rfl).hom =
            (pageTwoComparison X (Iso.refl _) p q (p + q) rfl).hom ≫
              (φ.hom (p + q)).app (ComposableArrows.mk₁
                (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))) →
        e' = e := by
  sorry

end CategoryTheory.Abelian.SpectralObject
