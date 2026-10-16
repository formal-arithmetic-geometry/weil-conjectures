# AlgebraicGeometry.strictHenselizationMapExists: unused public Henselian import

## Reason

The proof is constructed from the pointed-neighbourhood limit and scheme pullbacks.
Neither its signature nor its proof needs the Henselian API. A scratch compilation
without this import passed; retaining it would leave an unused public import.
The first dry run required a change record because removal changes the item's
exported imports, although all existing declaration signatures are identical.

## Old

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
```

## New

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.ResidueField
```

The theorem's complete signature, visibility and mathematical meaning are unchanged.
No definition, target statement, or statement dependency changes.
The three obsolete plain proof imports are removed as recorded in the report.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictHenselizationMapExists | C1 | Unused public import removed; theorem signature identical. |
| Sheaf.Paper.StrictHenselizationFunctoriality | holder not queried; not adapted | Direct importer. Independently publicly imports WeilConjectures.Mathlib.RingTheory.Henselian; original source compiles against the delivered module. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift | holder not queried; not adapted | Direct importer. Publicly imports StrictHenselizationCanonicalMap, which publicly imports StrictHenselizationFunctoriality and hence its Henselian API. Original source compiles against the delivered module. |

The source scan with tools/downstream.py found these two direct importers and 849
transitive importers in total. Both direct importers preserve access to the entire
removed export through their independent imports. Their exported declarations and
imports are unchanged, so every further downstream module has the same API access.
No downstream statement becomes weaker, stronger or different; no adaptation is
needed, and no other existing module is delivered. No target uses a changed definition.
The consumer check used scratch copies and lcompile.py, compiling the delivered item
first and then both original direct consumers against that overlay.

## Status

landed 20261016T221558-L-1611643 2026-10-16 (merge of deliver/C1/Sheaf.Paper.StrictHenselizationMapExists)
