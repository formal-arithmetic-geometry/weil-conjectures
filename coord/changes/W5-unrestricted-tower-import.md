# Sheaf.Paper.IntegralReductionTowerUnrestricted imports

## Reason

The unrestricted tower imported the legacy tower solely to obtain coefficient definitions
and the inverse-sequence API. That import pulled in the legacy well-definedness theorem,
preventing its proof from using the already proved unrestricted theorem. Replace the
incidental import with its actual prerequisites. No declaration, definition, hypothesis,
or conclusion changes. The module is unclaimed.

The old and new public import closures were compared, and source references in all
consumers were checked against each consumer's remaining direct imports and their public
closures. No consumer uses a declaration lost by this import change. In particular the
three direct importers retain their own prerequisites. No target meaning changes. The item keeps its existing public imports and all sixteen
public declaration signatures unchanged; the companion abbreviation refactoring is
documented separately.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.IntegralReductionTower
```

## New

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.CategoryTheory.Functor.OfSequence
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralReductionTowerUnrestricted --direct` lists
these three direct importers. Their transitive public consumers were also checked for
references to declarations in the removed public closure; no missing import was found.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | unclaimed | Import prerequisites directly. |
| Sheaf.Paper.IntegralOperationsWellDefined | G1 | No source or signature change. |
| Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted | unclaimed | Whisker the transition naturality proof with localization, avoiding witness expansion; signatures and public constructions unchanged. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | C7 | No source or signature change. |
| Sheaf.Paper.IntegralReductionTowerWellDefined | W5 | Can reuse the unrestricted proof without an import cycle. |

## Status

landed 20261019T192853-L-1878430 2026-10-19 (merge of deliver/W5/Sheaf.Paper.IntegralReductionTowerWellDefined)
