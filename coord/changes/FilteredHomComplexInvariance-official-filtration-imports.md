# CategoryTheory.filtered_hom_complex_invariance

## Reason

Restore the quarantined module assigned by coord/rework.tsv, preserving its seven
public declarations, its mathematical statement and its dependency plan. The upstream
sync added the official CanonicalFiltration and FiniteFiltrationInductionExtension
modules. The old Sheaf imports load duplicate constants into the same environment.
The preserved source failed with an IsExhaustive duplicate; replacing only the first
import still fails through the old finite-filtration module. Replacing both imports
compiles against the published server library in 1.2 seconds.

This is an import-provider repair, not a proof of the remaining invariance theorem.
The full non-import source text is identical to the quarantine copy. No upstream
source, target statement, definition body, declaration signature or visibility changes.
All mathematical edge cases, including zero complexes and empty filtration steps,
retain exactly the original hypotheses and conclusions.

## Old

```lean
public import Sheaf.CategoryTheory.Filtration
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
```

The archived item is quarantine/Sheaf/Algebra/Homology/FilteredHomComplexInvariance.lean.
It has one hole, CategoryTheory.filtered_hom_complex_invariance.

## New

```lean
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
```

The first official module supplies the same filtration compatibility API and the
category on the existing FilteredObject.Hom. The second supplies restrictionSteps,
exists_gradedMap_steps, gradedMapSteps and finite_filtration_induction_steps, with
exactly the original names and interfaces. The import of InjectiveTargetHomSymbol
and the FilteredComplexSubquotients dependency are retained. No DAG route changes.
The original Lean attachment is preserved. No target meaning changes or target
statement review is reopened.

## Users

A source scan of both library roots finds no active importers. The two archived
parents below import this module only for their planned proofs; neither source uses
its seven declaration names. Their own restoration and independent API migrations
remain their rework items. Restoring this dependency needs no edits to those files.
The source-only downstream tool with --allow-missing reports zero downstream modules
and zero users of CategoryTheory.filtered_hom_complex_invariance.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FilteredHomComplexInvariance | Q4 | Restore from quarantine and replace two public import providers; declarations unchanged. |
| Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse | unclaimed; quarantined | Proof import resolves again; no source or signature adaptation required by this repair. |
| Sheaf.Algebra.Homology.FilteredGlobalHomExactAdjunction | unclaimed; quarantined | Proof import resolves again; no source or signature adaptation required by this repair. |

## Status

landed 20261020T162320-L-3589204 2026-10-20 (merge of deliver/Q4/Sheaf.Algebra.Homology.FilteredHomComplexInvariance)
