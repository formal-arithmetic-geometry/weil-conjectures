/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! # Existence of the page-two map

Source: Mathlib Algebra/Homology/SpectralObject/{Page,SpectralSequence,FirstPage}.lean,
Stacks Project Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-map-extension).
(blueprint: lem-sp-spectral-object-page-two-map-existence)

Proof: construct the page components by applying the homology-map construction to the
three-term complexes defining each page object. Naturality of the connecting morphisms
proves compatibility with page differentials; the kernel and image universal properties
prove compatibility with successor-page homology isomorphisms and the displayed page-two
comparison equation.
-/

@[expose] public section

universe uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.SpectralObject

/-- A morphism of spectral objects induces a morphism of their canonical `E₂` spectral
sequences satisfying the page-two comparison equation. The construction uses the
kernel/image maps on the three-term complexes defining `pageX`; the compatibility
of connecting morphisms gives the differential and successor-page equations.
Source: Mathlib Algebra/Homology/SpectralObject/{Page,SpectralSequence,FirstPage}.lean,
Stacks Project Tags 012K and 015K (blueprint: lem-sp-spectral-object-page-two-map-extension).
(blueprint: lem-sp-spectral-object-page-two-map-existence)

Proof: construct the page components by applying the homology-map construction to the
three-term complexes defining each page object. Naturality of the connecting morphisms
proves compatibility with page differentials; the kernel and image universal properties
prove compatibility with successor-page homology isomorphisms and the displayed page-two
comparison equation.
-/
theorem exists_pageTwoMap_data
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {X Y : SpectralObject C EInt} (φ : X ⟶ Y) :
    ∃ e : X.E₂SpectralSequence ⟶ Y.E₂SpectralSequence,
      ∀ (p q : ℤ),
        (e.hom 2).f (p, q) ≫
            ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            Y.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom =
          ((HomologicalComplex.eval C _ (p, q)).mapIso
              ((SpectralSequence.pageFunctor C _ 2 2).mapIso (Iso.refl _)) ≪≫
            X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) _ _ rfl rfl
              (p + q) rfl).hom ≫
            (φ.hom (p + q)).app (ComposableArrows.mk₁
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))) := by
  sorry

end CategoryTheory.Abelian.SpectralObject
