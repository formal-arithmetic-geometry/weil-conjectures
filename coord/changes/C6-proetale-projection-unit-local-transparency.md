# proEtaleRingModuleAdjunction (local transparency in ProEtaleProjectionFormulaArrows)

## Reason

The unit normalization proof uses the canonical adjunction abstractly. Unfolding its
uniquely selected construction makes elaboration unnecessarily expensive. A local
irreducibility registration keeps it abstract during this theorem's proof. Preflight
classifies this command as an interface change and requires this record.

The registration is confined to `section ProjectionUnitProof`. It changes no existing
signature, definition body, visibility, public import, or target statement, and an
importer does not inherit it. The three new private lemmas are fully proved and occur
only in the theorem's proof. No consumer adaptation is needed.

## Old

No local transparency registration for `proEtaleRingModuleAdjunction` in this module.
The imported declaration is unchanged:

```lean
noncomputable def proEtaleRingModuleAdjunction :
    proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c :=
  Classical.choose (proEtaleRingModuleAdjunction_existsUnique f R S c)
```

## New

The imported declaration remains exactly as above. Inside `section ProjectionUnitProof`:

```lean
attribute [local irreducible] proEtaleRingModuleAdjunction
```

The section ends immediately after `proEtaleProjectionUnit_existsUnique`, restoring
its original transparency for the remaining declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleProjectionFormulaArrows | C6 | Local elaboration only; the unit normalization theorem keeps its exact signature. |

`tools/downstream.py Sheaf.Paper.ProEtaleProjectionFormulaArrows --uses
proEtaleProjectionUnit_existsUnique` reports one module using the declaration: the
item itself (two occurrences). There are 1525 downstream modules in the import graph;
none inherits this local attribute or sees any changed signature, so all their
statements retain their meaning. No module outside the item is adapted.

## Status

landed 20261019T192656-L-1853845 2026-10-19 (merge of deliver/C6/Sheaf.Paper.ProEtaleProjectionFormulaArrows)
