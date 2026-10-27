# CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison

## Reason

The delivery proves the comparison theorem with new private helpers. Ten `omit ... in`
commands restrict section assumptions only for the private lemma immediately following
each command. The static interface checker classifies these new top-level commands as
an interface change and requests this record. There is no change to any public signature,
public definition, instance, attribute, notation, or public import. Every existing consumer
has the same elaboration interface. No target meaning or statement changes.

## Old

The module had no scoped `omit ... in` commands. Its comparison theorem signature was:

```lean
theorem internalModuleInverseImageComparison :
    (inverseBraided J K f A B adj unit_eq).toMonoidal.toOplaxMonoidal =
        inverseOplax J K f A B adj ∧
    TensorNormalization J K f.inverse A
      (inverseBraided J K f A B adj unit_eq).toMonoidal.toLaxMonoidal ∧
    ComparisonStatement J K f A (inverseBraided J K f A B adj unit_eq)
```

## New

The comparison theorem has the same signature, with a proved body:

```lean
theorem internalModuleInverseImageComparison :
    (inverseBraided J K f A B adj unit_eq).toMonoidal.toOplaxMonoidal =
        inverseOplax J K f A B adj ∧
    TensorNormalization J K f.inverse A
      (inverseBraided J K f A B adj unit_eq).toMonoidal.toLaxMonoidal ∧
    ComparisonStatement J K f A (inverseBraided J K f A B adj unit_eq)
```

The new scoped commands immediately precede only these private lemmas:
`pairSource_fst`, `pairSource_snd`, `underlying_hom_inv`, `underlying_inv_hom`,
`abelianPair_add`, `underlying_inv_naturality`, `transport_bilinear`, `transport_one`,
`abelianPair_bilinear`, and `terminalSource_one`. The omitted section instances are
`UnivLE`, `HasSheafify`, and the monoidality of local equivalences, where the particular
private helper does not use them. Each command ends with `in`, so it changes only the
following private declaration. The declaration-scoped heartbeat option likewise affects
only checking `comparison_of_normalization`. All private helper statements and proofs are
included in the item module. None appears in a public statement or public definition body.

## Users

`tools/downstream.py Sheaf.CategoryTheory.InternalModuleInverseImageComparison --uses
CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison` lists
four downstream modules. No adaptations are required: all original public declarations,
public imports and global commands remain unchanged. The theorem itself is the only
textual user returned by the declaration-use search.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InternalModuleInverseImageComparison | H3 | Proof added; scoped commands affect private helpers only. |
| Sheaf.Paper.ContinuousAlgclScalarConstructibility | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.InternalScalarMateTransitivity | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.InternalScalarPullbackNormalization | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | unclaimed | No signature or definition change; no adaptation. |

## Status

landed 20261022T202025-L-1250067 2026-10-22 (merge of deliver/H3/Sheaf.CategoryTheory.InternalModuleInverseImageComparison)
