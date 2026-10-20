# CategoryTheory.FiniteFilteredDerivedPlus

## Reason

Restore the quarantined zero-hole module after the upstream filtration synchronization.
Its unnecessary public import of
`WeilConjectures.Algebra.Homology.FilteredComplexSubquotients` combines the upstream
canonical filtration with an older published build of the Sheaf filtration API,
causing the recorded duplicate `DecreasingFiltration.IsExhaustive` import error.
No declaration in this module uses the subquotient API. Removing that import
repairs the import collision while keeping every declaration, definition and proof.
The canonical filtration build was also checked by compiling current
FiniteFiltrationInduction and FiniteFilteredGradedExactness sources before this module.

## Old

```lean
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
```

## New

The unused public import is removed. All existing signatures and definition bodies
are unchanged. FiniteFiltrationInduction supplies the filtered-object and graded-map API.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FiniteFilteredLocalization --uses
CategoryTheory.FiniteFilteredDerivedPlus` lists no current library users: the module
is absent from lean/ under its rework assignment. The archived direct users were
also inspected. FilteredDerivedHomCalculus is restored with an explicit public
import of the removed module; its signatures, definitions and proofs are unchanged.
The other archived consumers are not changed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.FilteredDerivedOperationLifts` | unclaimed | Archived; already imports FilteredComplexSubquotients explicitly. |
| `Sheaf.Algebra.Homology.UniformFilteredHomotopyLocalization` | unclaimed | Archived; does not use the removed subquotient API. |
| `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel` | unclaimed | Archived; does not use the removed subquotient API. |
| `Sheaf.Algebra.Homology.FilteredInjectiveResolution` | unclaimed | Archived; does not use the removed subquotient API. |
| `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus` | unclaimed | Restored with explicit public import FilteredComplexSubquotients for complexQuotientπ; no other changes. |
| `Sheaf.Algebra.Homology.FilteredAcyclicInjectiveVanishing` | unclaimed | Archived; does not use the removed subquotient API. |
| `Sheaf.Algebra.Homology.FilteredConeLocalization` | unclaimed | Archived; does not use the removed subquotient API. |

This changes the import interface, not the meaning of any target or definition.
All DAG attachments and dependencies are retained. No module is withdrawn.

FiniteFiltrationInduction and FiniteFilteredGradedExactness are included byte for
byte from current library sources to rebuild the synchronized canonical API in
the combined compile. Neither is adapted, and neither adds a hole.

The consumer's exact change is the addition of:

```lean
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
```

The original consumer needs complexQuotientπ in the public signature of its
calculus. With the item's redundant import removed, this explicit public import
is the correct owner of that statement dependency. It is unclaimed.
Its ten existing archived theorem holes are retained and reported.
A counterfactual single-file compile of the unchanged archived consumer against
the repaired item fails at line 376: Invalid field complexQuotientπ; the environment
does not contain CategoryTheory.DecreasingFiltration.complexQuotientπ. The adapted
consumer compiles in 10.6 s, confirming that this import adjustment is necessary.

## Status

landed 20261020T162548-L-3622695 2026-10-20 (merge of deliver/P2/Sheaf.Algebra.Homology.FiniteFilteredLocalization)
