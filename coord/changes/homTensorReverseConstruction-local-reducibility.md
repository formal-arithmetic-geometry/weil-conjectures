# homTensorReverseConstruction local reducibility

## Reason

The delivered proof must avoid repeatedly unfolding the chosen Hom-complex bifunctor
and its chosen product projections. Add local irreducibility attributes after a proved
private lemma identifies the product specification. The preflight's command scanner
classifies any attribute command as a possible interface change, hence this record.
All attributes are explicitly local: no downstream interface, statement, definition,
or reducibility behavior changes. No consumer requires an adaptation.

## Old

No local reducibility command. The original theorem was `:= by sorry`.
The existing theorem signature is unchanged, verbatim, in the delivered module.

## New

```lean
-- Do not unfold the chosen bifunctor while checking localized section formulas.
attribute [local irreducible] homComplex homComplexFunctor homTensorCurryProjection
```

The attributes apply only in this module after `hom_product_spec` is proved.
The new helpers HomTensorReversePair and InternalHomProduct are proof imports,
so neither their imports nor their new declarations become visible to importers.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.HomTensorReverseConstruction --uses
homTensorDegreewise_reverse_construct` reports 519 transitive module importers,
but only the following external textual user and direct importer. Every transitive
importer sees the identical public signature and the identical public imports.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.HomTensorDegreewiseIso | unclaimed | No change: the theorem signature and public imports are identical, and the attributes are local. No adaptation. |

The item's own occurrence of the declaration is its definition, not an external user.

## Status

landed 20261013T154359-L-1163715 2026-10-13 (merge of deliver/W3/Sheaf.Algebra.Homology.HomTensorReverseConstruction)
