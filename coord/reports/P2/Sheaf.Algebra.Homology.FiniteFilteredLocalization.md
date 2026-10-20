## What changed

Restored Sheaf.Algebra.Homology.FiniteFilteredLocalization from quarantine,
preserving all 25 public declarations and the existing DAG attachment. Removed
its unused public import of
WeilConjectures.Algebra.Homology.FilteredComplexSubquotients, which caused the
recorded collision between the canonical filtration and the older published
Sheaf filtration API. No declaration signature, definition or proof changed.

Adapted the unclaimed archived consumer
Sheaf.Algebra.Homology.FilteredDerivedHomCalculus by restoring it with an explicit
public import of FilteredComplexSubquotients, which its public calculus uses
through complexQuotientπ. This is its only source change. Its existing ten
archived theorem holes are retained. No other consumer needs an adaptation.

FiniteFiltrationInduction and FiniteFilteredGradedExactness are included unchanged
from current library sources so the combined compile rebuilds the synchronized
canonical API. They have zero holes and no source changes. The four-module packet
compiles cleanly: 12.2 s for the item and 10.6 s for its adapted consumer.
The item also compiles against the published build without overrides (8.4 s).
A counterfactual compile of the unchanged archived consumer against the repaired
item fails at line 376: Invalid field complexQuotientπ; the environment does not
contain CategoryTheory.DecreasingFiltration.complexQuotientπ. The one-line
explicit-import adaptation compiles, establishing its necessity.
Change record: coord/changes/P2-finite-filtered-localization-import.md.
Quarantine archives and all Lean attachments and node dependencies are preserved.

## Proved and sorry left

Assigned item: zero original holes; holes closed 0 of 0; holes remaining 0.
No proof is newly claimed, and no result is split off.

The restored consumer retains these ten pre-existing archived holes, all under
node lem-trf-filtered-derived-hom-calculus and namespace
CochainComplex.FiniteFiltered:

- graded_laws
- truncation_bounds
- restriction_square
- truncation_maps
- cone_antitone
- shift_antitone
- cone_shift_bounds
- cone_maps
- shift_preserves
- filteredDerivedHomCalculus

There are no new theorem statements or holes relative to the quarantine sources.
Relative to the current active library, restoring the consumer adds those ten
existing holes. The other three delivered modules have no holes. This is an
interface repair, not a proof/decomposition progress claim.

## No longer needed

Removed from the item: public import
WeilConjectures.Algebra.Homology.FilteredComplexSubquotients. None of its
complexStep, complexQuotient, complexQuotientπ, complexCycleRepresentatives,
complexCycles or complexBoundaries operations is used in the item. The direct
consumer needing that API now imports its owner explicitly. The finite graded
exactness proof dependency remains necessary.

There are no active library importers. All seven archived direct importers were
inspected. FilteredDerivedOperationLifts already imports the subquotient module
explicitly; FilteredDerivedHomCalculus is adapted in this packet. The other five
(UniformFilteredHomotopyLocalization, FilteredLocalizationInjectiveModel,
FilteredInjectiveResolution, FilteredAcyclicInjectiveVanishing,
FilteredConeLocalization) do not use the removed API. The change record lists all
users and their claim status. No node or module is withdrawn, and all DAG
statement and proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The assigned archive has zero sorries, despite the generic prove brief and the
queue's hole estimate. Its assigned problem is a real import collision after
synchronization. The retained constructions and proofs also compile with current
canonical filtration dependency sources. The unused subquotient import causes
the collision against the still-mixed published build; it belongs in the consumer
that actually uses it. Mathematical statements and the unit route are unchanged.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
