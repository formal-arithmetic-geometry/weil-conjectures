# exists_proper_flat_cohomology_model_data_construction

## Reason

The unchanged statement only needs the definition of IsFlatOver from DirectImage.Basic.
The proof uses an affine neighbourhood and the zero complex; Sections and its higher-direct-image
results are unnecessary. Narrow the public import to Basic, and add a proof-only import of the
proved quasi-coherence result for free sheaves. Retain the explicit separated-morphism import.
The unused-variable linter is disabled only at the theorem, because its unchanged explicit hF
hypothesis is unnecessary for its actual conclusion. This is not a statement or definition change.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
```

The theorem's signature, visibility, universes, hypotheses and conclusion are identical.
Its docstring now explains the termwise conclusion and the actual proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyData | unclaimed | Unaffected: the sole direct importer already publicly imports DirectImage.Sections itself, and uses precisely the unchanged theorem signature. |

Read tools/downstream.py with --uses exists_proper_flat_cohomology_model_data_construction:
the only external module mentioning this declaration is the direct importer listed above.
No downstream theorem statement or definition changes; no adaptation is needed.
No target definition changes, and no target statement is changed.

## Status

landed 20261012T202233-L-702385 2026-10-12 (merge of deliver/D2/Sheaf.AlgebraicGeometry.ProperFlatCohomologyDataConstruction)
