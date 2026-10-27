# AlgebraicGeometry.etale_fibre_product_pair_refinement

## Reason

The proof uses only Mathlib. Remove the unrelated BaseChangeConventions source-library
import and redundant imports, and expose Separated directly because the existing
statement mentions IsSeparated. The theorem signature and all instances and attributes
are unchanged. No existing source-library file is changed.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleFibreProductPairRefinement | D3 | Proof completed; statement unchanged. |
| Sheaf.AlgebraicGeometry.CoherentFormalGenerationFlatness | unclaimed | Sole direct importer, copied unchanged and compiled successfully against the new module (13.4 s); no adaptation needed. |

The DAG parent Sheaf.AlgebraicGeometry.MinimalSmoothEnvelopeComparison is currently
absent from lean and does not import the module. Its node and this item's attachment
and dependencies are preserved; no withdrawal is requested.

## Status

landed 20261026T091345-L-3336123 2026-10-26 (merge of deliver/D3/Sheaf.AlgebraicGeometry.EtaleFibreProductPairRefinement)
