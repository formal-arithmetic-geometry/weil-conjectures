# AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars

## Reason

The stage-3 static visibility check requests a change record because the proof adds
scoping commands (`namespace`, `open`, and local `attribute` commands) inside the
source module's existing public section. This record documents those commands and
the complete consumer audit. They support the new proof and do not alter any existing
signature, definition, visibility, public import, or global attribute.

## Old

The existing instance signature, verbatim:

```lean
instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
```

Its body was `sorry`. The file already used `@[expose] public section`, opened
`CategoryTheory MonoidalCategory MonObj`, and had namespace `AlgebraicGeometry.ProEtale`.

## New

The instance has exactly the same signature:

```lean
instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
```

Its body is now proved. New helper theorems are all private and proved; none occurs in
an existing public signature or the data of a public definition. Their lexical namespaces
are closed before the original declarations resume. `Limits` is added to the file's
local open namespaces, with further local opens inside the closed helper namespaces.

For proof elaboration only, the file installs these local reducibility attributes:

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
```

These attributes expire at the end of their lexical scope and do not change any
importer-visible definition or global attribute. They keep the large pullback and
derived-functor constructions abstract while their already proved APIs are used.
Every added import is private. The instance, original preservation lemma, coefficient
objects, coefficient inclusion, restricted scalar extension, compatibility isomorphism,
rationalization equivalence and comparison isomorphism retain their original statements
and definitions. No target meaning changes and no target statement review is reopened.

## Users

`tools/downstream.py
WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization --uses
AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars`
reports one downstream module, `WeilConjectures`. Its only use is the existing aggregate
import of this module. The declaration-name scan has no external hit. All existing
coefficient/functor definitions and both equivalence definitions were compared verbatim
to the original and are unchanged. Public imports are identical. No consumer statement
becomes weaker, stronger, or different, so no adaptation is forced.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | F1 | Sole existing hole closed; new private proof helpers and lexical commands only. |
| WeilConjectures | unclaimed | Same aggregate import and identical existing exported declarations; no adaptation. |

## Status

landed 20261018T101338-L-3972760 2026-10-18 (merge of deliver/F1/WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization)
