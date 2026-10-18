# AlgebraicGeometry.Scheme.localIsomorphismMap_laws

## Reason

The static interface checker flags the added section and local attribute commands.
They scope proof elaboration: making `Etale.upperStar` locally irreducible prevents
unwanted unfolding during derived-category coherence calculations. Existing public
signatures, definitions, instances, imports and visibility are unchanged. The added
import is proof-only. No target meaning changes and no consumer adaptation is needed.

## Old

Immediately after `localIsomorphismMap`, there was no additional section or attribute.
The proof of `localIsomorphismMap_laws` was `by sorry`.

## New

```lean
section RestrictionLaws

attribute [local irreducible] Etale.upperStar
```

Private proved coherence helpers and the complete proof of the existing theorem
follow. `end RestrictionLaws` precedes `derivedLocalIsomorphismPresheaf`, restoring
the previous transparency environment. Declaration-local elaboration options are
introduced with `set_option ... in`; they do not persist beyond each proof.

## Users

`tools/downstream.py Sheaf.Paper.DerivedLocalIsomorphismSheaf --uses localIsomorphismMap_laws`
reports the item itself as the sole direct user of the theorem and the following
single downstream module. No existing definitions or signatures change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedLocalIsomorphismSheaf | W3 | One proof completed; signatures unchanged. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Same public interface; local attribute has ended before the presheaf definition. |

## Status

landed 20261018T145122-L-3647711 2026-10-18 (merge of deliver/W3/Sheaf.Paper.DerivedLocalIsomorphismSheaf)
