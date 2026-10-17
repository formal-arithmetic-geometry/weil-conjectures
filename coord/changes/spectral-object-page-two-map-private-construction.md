# CategoryTheory.Abelian.SpectralObject.exists_pageTwoMap_data

## Reason

Fully construct the spectral-sequence morphism from the homology maps of the
three-term complexes, and prove its page-two comparison. The conservative interface
check flags added `universe`, `variable`, `open`, section and scoped option commands.
These support private helpers only. No existing public signature, definition or
public import changes. The extra `import all` is proof-only and permits use of
Mathlib's canonical homology data with private proof constants in dependent types.
All helper definitions are explicit constructions, and all helper lemmas are proved.
The private lemmas have no added simp attributes.

## Old

```lean
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
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))
```

The proof was `by sorry`. The file declared only universes `uC vC` and had no
helper sections.

## New

```lean
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
              (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt))))
```

The proof supplies a privately constructed spectral-sequence morphism. Added local
helper contexts use universes `uI vI`, `open Category Limits ComposableArrows`, and
explicit section variables for general spectral-object and page data. Each helper
is private; its sections end before this unchanged theorem. The transparency option
and `unseal` commands are scoped to individual helper declarations.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence --uses
exists_pageTwoMap_data` found the following textual users. There are 502 transitive
downstream modules; all retain the same public theorem and public imports, and none
requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence | H4 | Assigned module; unchanged public statement, now proved. |
| Sheaf.CategoryTheory.SpectralObjectPageTwoMap | unclaimed | Its application of `exists_pageTwoMap_data` remains valid verbatim. |

The consumer defines the canonical map by the unique witness of the unchanged
existence theorem. Its properties and uniqueness proof are unaffected by the choice
of this explicit witness. No consumer or target definition was changed.

## Status

landed 20261017T044846-L-2996845 2026-10-17 (merge of deliver/H4/Sheaf.CategoryTheory.SpectralObjectPageTwoMapExistence)
