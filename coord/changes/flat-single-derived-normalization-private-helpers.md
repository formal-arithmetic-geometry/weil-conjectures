# SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization

## Reason

The interface-command checker conservatively flags the scoped `variable` commands introduced
for private generic collapse lemmas. They are enclosed in `section GenericCollapse` and
`end GenericCollapse`; their variables cannot affect the existing declarations that follow.
All newly introduced declarations are private and proved. The public theorem, abbreviations,
public imports and mathematical meanings are unchanged. This record documents the command
scope recognized by preflight; it authorizes no statement or definition change.

## Old

No generic-helper section occurred between `collapse` and the derived-category instance binder.
The existing binder was, verbatim:

```lean
variable [HasDerivedCategory.{w} (KFlatFixedTensor.Modules R)]
```

## New

Before the same existing binder, private proofs are grouped with these scoped commands:

```lean
section GenericCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]
```

After the private collapse abbreviation and projection proof:

```lean
variable [∀ X, (T.flip.obj X).Additive]
```

After the private shift proof:

```lean
end GenericCollapse
```

These commands parameterize only private helpers. Their full proofs are in the delivered
module. The unchanged public theorem is proved from them and the existing dependency APIs.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FlatSingleDerivedNormalization --uses
SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization` reports zero
downstream modules and only the declaration's own module as a textual user.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FlatSingleDerivedNormalization | A4 | Original public signatures and definitions retained; the theorem's original hole is filled; added helper variables are confined to their private section. |

No consumer adaptation is required. No target meaning or source-library file changes.

## Status

landed 20261022T142401-L-729029 2026-10-22 (merge of deliver/A4/Sheaf.Algebra.Homology.FlatSingleDerivedNormalization)
