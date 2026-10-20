# CategoryTheory.filteredHomologyCouple_normalization

## Reason

Restore the quarantined normalization theorem after upstream sync and prove its
single hole. Its public statement mentions `BigradedExactCouple.initialG`, so
`ExactCoupleConvergence` must be publicly imported. The archived private import
caused the recorded `lean.invalidField` error even before elaborating the proof.
The theorem signature and its mathematical meaning are unchanged.

## Old

```lean
public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
import Sheaf.CategoryTheory.FilteredHomologyCoupleData
import WeilConjectures.CategoryTheory.ExactCoupleConvergence
```

## New

```lean
public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
```

The separate `FilteredHomologyCoupleData` import is redundant: it is already
publicly imported by `FilteredHomologyExactCouple`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredHomologyCoupleNormalization | J4 | Restored; unchanged signature, complete proof, required public import. |
| Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure | unclaimed, quarantined | Sole archived direct importer and theorem user; its application receives exactly the same existential and equations. No adaptation. |

`tools/downstream.py` finds no live importers: this module and its only archived
direct importer are quarantined. Searching both library roots and quarantine
finds only the two modules listed above. No source-library declaration, target,
definition, or target meaning changes. The larger transitive quarantine entries
in `coord/rework.tsv` remain separate repair items.

## Status

landed 20261020T145519-L-2405500 2026-10-20 (merge of deliver/J4/Sheaf.CategoryTheory.FilteredHomologyCoupleNormalization)
