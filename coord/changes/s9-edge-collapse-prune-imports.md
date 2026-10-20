# CategoryTheory.BigradedExactCouple.edge_collapse

## Reason

Prove the existing theorem without changing its signature or definitions. Its signature
needs only the public convergence module, whose public dependency chain supplies the
bigraded exact couple and the PBC image filtration actually used in this theorem.
The withdrawn Sheaf exact-couple compatibility module supplies no declarations, and
Sheaf.CategoryTheory.Filtration supplies a different compatibility API that this theorem
does not use. Remove both unused public imports. Add a private proof import for the
proved subobject pullback-factorization criteria used to identify the pullback of zero
with the kernel.

## Old

```lean
public import Sheaf.CategoryTheory.ExactCouple
public import Sheaf.CategoryTheory.Filtration
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
```

## New

```lean
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru
```

The theorem signature and docstring remain verbatim. Every added helper is private and
fully proved. No definition, instance, target statement, or source-library module changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.EdgeCollapse | S9 | One hole closed; two unused imports removed. |

`python3 tools/downstream.py Sheaf.CategoryTheory.EdgeCollapse --uses
CategoryTheory.BigradedExactCouple.edge_collapse` reports zero downstream modules and
only this theorem's declaration as a textual use. Searching both library roots agrees.
No consumer adaptation is required. The import-direction check permits the added private
proof import. The current DAG dependencies remain needed and unchanged: exact couples,
convergence, and filtrations are still used through the upstream convergence module.
No module is withdrawn or deleted.

## Status

landed 20261020T151233-L-2652305 2026-10-20 (merge of deliver/S9/Sheaf.CategoryTheory.EdgeCollapse)
