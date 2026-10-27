# AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.insertion_additive

## Reason

The insertion proof uses the specified gluing data through its normalization properties.
Keeping its four data definitions irreducible before that proof avoids unfolding their
nested choice terms. They already have the same global irreducibility attribute later in
the original file. Moving that command earlier changes only elaboration inside this file.

The sectionwise `SheafOfModules.pushforward` construction is expensive to unfold repeatedly
in the insertion statements and proofs. Keeping it locally irreducible after the restriction
exactness proof reduced a full compile from 54.7 seconds (and a delivery timeout) to 36.0
seconds. It remains reducible within the restriction proof where the construction is needed.
This local attribute is not exported. No definition body or public signature changes.

## Old

After `attribute [instance] insertion_additive`:

```lean
attribute [irreducible] gluing moduleUnit moduleCounit insertion
```

No local irreducibility attribute on `SheafOfModules.pushforward`.

## New

Immediately after the definition of `insertion`, before `insertion_additive`:

```lean
attribute [irreducible] gluing moduleUnit moduleCounit insertion
```

Immediately after the proof of `restriction_exact`:

```lean
attribute [local irreducible] SheafOfModules.pushforward
```

All four data definitions and all theorem signatures are verbatim. The exported attributes
on those definitions at the end of the file are identical to the original attributes.
The new helpers are private proved theorems and the new imports are proof-only imports.
No target meaning or unit route changes.

## Users

`tools/downstream.py` lists the following four downstream modules. Its `--uses insertion`
and `--uses gluing` searches find no downstream references. The two scalar modules use the
unchanged `restrictionLimits` and `restrictionColimits` instances. The completed-operation
and composite-counit modules retain exactly the same interface and global attributes.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization` | A9 | Three theorem proofs; earlier irreducibility boundary and local pushforward boundary. |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor` | unclaimed | No signature or definition changes; no adaptation needed. Final exported attributes are identical; the pushforward attribute is local. |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent` | unclaimed | No signature or definition changes; no adaptation needed. Final exported attributes are identical; the pushforward attribute is local. |
| `Sheaf.Paper.ClopenCompletedOperationTowers` | unclaimed | No signature or definition changes; no adaptation needed. Final exported attributes are identical; the pushforward attribute is local. |
| `Sheaf.SixFunctors.ClopenCompositeCounitNormalization` | unclaimed | No signature or definition changes; no adaptation needed. Final exported attributes are identical; the pushforward attribute is local. |

## Status

landed 20261023T151759-L-408009 2026-10-23 (merge of deliver/A9/Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization)
