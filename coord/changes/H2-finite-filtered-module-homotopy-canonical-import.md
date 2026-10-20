# finiteFilteredModuleHomotopy canonical import restoration

## Reason

Restore the assigned zero-hole module from its quarantine archive. Compiling the
archive reproduces the recorded failure at the module header:

```text
import Sheaf.CategoryTheory.Filtration failed, environment already contains
'CategoryTheory.DecreasingFiltration.IsExhaustive' from
WeilConjectures.CategoryTheory.CanonicalFiltration
```

The archive combines the canonical upstream filtration imported by
`FilteredComplexSubquotients` with the old compiled Sheaf induction route.
The adopted source library already provides the complete induction extension
against `CanonicalFiltration`. Use that existing module instead of importing the
obsolete duplicate route. The repaired item compiles in 1.0 seconds. All five restored declarations pass
`#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

## Old

```lean
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
```

## New

```lean
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
```

This is the sole change to the archived Lean source. All five declaration bodies,
signatures, docstrings and other imports are retained verbatim. The canonical
filtration, filtered morphisms, finite bounds, graded maps, filtered homotopies,
quotient category and quasi-isomorphism predicate retain their meaning. No data
is chosen from an unproved existence theorem, and no target statement changes.
The item's existing node retains its attachment and dependencies; its Lean note
records the import migration.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy` reports an unknown module,
because the item is quarantined and absent from the live `lean/` tree. A direct
import and declaration-use search of both `lean/` and `quarantine/` finds no live
users and the following ten quarantined direct importers. Their restoration is
tracked independently in `coord/rework.tsv`; none is withdrawn by this repair.
The queue records 36 quarantined importers in the transitive closure.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy | H2 | Restore all five declarations; repair the import collision; zero holes. |
| Sheaf.Algebra.Homology.CanonicalTruncationFiltration | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.DerivedCanonicalFiltration | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredPageLocalization | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredProjectiveComparison | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredQuasiIsoFractions | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredQuasiIsoRightCancellation | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredQuasiIsoRightOre | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FilteredTensorLocalization | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |
| Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement | unclaimed; quarantine | Public names and mathematical meanings preserved; no source adaptation in this repair. |

The unmodified archived `FilteredQuasiIsoRightCancellation`,
`FilteredQuasiIsoRightOre`, `FilteredQuasiIsoTwoOutOfThree`, and
`FilteredQuasiIsoFractions` compile against the repaired item in an isolated
scratch consumer set. Existing holes in those archived consumers are unchanged
and are not part of the delivery. Other quarantined consumers still have their
separately recorded upstream migration work (some mention the retired
`HomPreservingSteps` API); the item change introduces no replacement type or new
signature. The existing upstream declarations are preserved, with no edits to
`lean/WeilConjectures/`.

## Status

landed 20261020T162543-L-3621385 2026-10-20 (merge of deliver/H2/Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy)
