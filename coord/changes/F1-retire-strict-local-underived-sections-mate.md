# StrictLocalUnderivedSectionsMate: retire the upstream re-export

## Reason

The current queue assigns retirement: coord/retire-items.tsv lists this wrapper and
its official upstream twin, under the human's hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The wrapper has no local declarations
and zero proof holes. It already publicly imports the complete canonical-model
implementation. Complete the retirement by migrating its sole live importer to that
identical provider and withdrawing the redundant path.

The historical DIFFERENT classification predates this re-export. The current DAG
attachment is the separate StrictLocalSmallModel implementation, which states the
original small-colimit-model result. Preserve that attachment and every mathematical
dependency; importing the canonical implementation is not a proof of that different
statement. The node changes only lean.note to document this path retirement.

## Old

The withdrawn module is, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate

/-! # The underived mate on pointed neighbourhood sections

The adopted source supplies `strictLocalUnderivedMateSections` and its proved
comparison `strictLocalUnderivedMateSections_eq`. Re-export that implementation
so that the neighbourhood restriction, the base-change square, and the cone legs
all use `Scheme.strictLocalization` and `Scheme.strictLocalizationToBase`.

The construction is restriction on the base, followed by global sections of the
underived exchange map and the direct-image/global-sections comparison. Its
comparison theorem identifies this map with restriction along the cone leg.
Both declarations retain their existing qualified names and mathematical content.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate).
-/

@[expose] public section

```

Its sole live importer contains:

```lean
import Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/StrictLocalUnderivedSectionsMate.lean through
deleted.txt. The delivery tool represents withdrawal by an empty module. The live
consumer imports the wrapper's existing public provider directly:

```lean
import WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate
```

All existing qualified names, types, definition bodies and proofs remain identical.
The adopted source and Challenge.lean are untouched. This is only import-path
retirement and requires no target semantic change. In particular the canonical
strictLocalization and the separate small-colimit model are not interchanged.

## Users

The read-only tools/downstream.py census found 13 live downstream modules.
A direct import scan found one live importer and the historical quarantined
StrictLocalDerivedMateSectionsFactorization archive. Declaration-use search found
zero live downstream uses of strictLocalUnderivedMateSections_eq. The full live
census follows; holder information is from the shared claims at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | F1 | Withdraw the zero-declaration re-export. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | unclaimed | Only private import changes to the same upstream provider; statement and proof unchanged. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnitGerm | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Transitive consumer; identical upstream API remains available; no edit. |
| WeilConjectures.AlgebraicGeometry.StrictLocalUnderivedSectionsMate | adopted source; unchanged | Existing complete canonical-model provider. |
| Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization | quarantined; unclaimed | Historical importer absent from lean; archive preserved. Its restored SmallModel counterpart imports the separate SmallModel mate module. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Current DAG realization; existing proved small-model construction and comparison preserved verbatim. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | DAG parent and direct SmallModel importer; preserved verbatim. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | DAG parent and direct SmallModel importer; preserved verbatim. |

The third DAG parent is the ordinary-germ consumer being adapted. Its original
mathematical dependency is retained while its unfinished proof sees the same
canonical API through a direct import. The other archived original-model parents
and all rework records remain intact. The unit sk-prop-h2 has no realized statement
or proof step attached to the retiring wrapper; its route is unchanged.

Validation through lcompile.py: the original consumer compiled in 1.9 seconds,
the adapted consumer in 2.1 seconds, and the canonical definition/full-comparison
probe in 1.7 seconds. Both canonical declarations use only propext, Classical.choice
and Quot.sound. Delivery preflight checks the withdrawal and consumer atomically.
No new theorem or new hole is introduced.

## Status

landed 20261022T184439-L-3703442 2026-10-22 (merge of deliver/F1/Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate)
