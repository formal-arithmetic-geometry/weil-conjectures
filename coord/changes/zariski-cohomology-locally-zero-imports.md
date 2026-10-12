# AlgebraicGeometry.zariski_cohomology_class_locally_zero

## Reason

The proof computes cohomology over each open in the original site by Ext from the
sheafified free abelian representable. It does not restrict injectives to an open
subscheme. Remove the unused public import of the open-restriction module and
import the Mathlib declarations needed for the unchanged signature directly.
All new helpers are private, fully proved, and absent from public signatures.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
```

The existing theorem signature and all its hypotheses are unchanged.

## New

```lean
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
```

This is an import-pruning record, with no changed definition or statement.
No target meaning changes and no target statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero | K1 | Same signature; complete proof. |
| Sheaf.Paper.GabberCriterion | none identified | Direct proof import; no use of removed declarations. |
| Sheaf.Paper.GabberCriterionDegree | none identified | Direct proof import; no use of removed declarations. |

`tools/downstream.py ... --uses zariski_cohomology_class_locally_zero` reports
only the declaring module as a textual use. The two direct importers above were
read; neither refers to any of the removed open-restriction declarations. There
are 140 transitive downstream modules. The import-pruning check examines those
modules for declarations lost through this change; no adaptations are needed.
The direct imports of this module in the two users are private proof imports,
so they do not expose its imports to their own importers.

## Status

landed 20261012T070541-L-3472962 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero)
