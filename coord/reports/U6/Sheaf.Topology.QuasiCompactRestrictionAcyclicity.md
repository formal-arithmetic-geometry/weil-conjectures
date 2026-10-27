## What changed

Proved `TopCat.Sheaf.subsingleton_H'_of_quasiCompact_restriction_surjective`
in `Sheaf.Topology.QuasiCompactRestrictionAcyclicity`, preserving its statement
and public imports. The proof restricts to the open subspace, transfers the compact
basis, intersections and restriction surjectivity along the open embedding, and
applies the existing site Čech vanishing criterion to finite compact-open covers.
Surjectivity onto unions of nonempty finite intersections follows from finite
union compactness and the given restriction hypothesis. Empty opens and covers
are included; no separation or ambient compactness assumption is added.

Repaired the return of head `620927ceb45`: removed the duplicate private
`TopCat.Sheaf.compact_basis_cofinal` and
`TopCat.Sheaf.compact_cech_intersections`. The item now privately imports
`Sheaf.Topology.FilteredInjectiveCechAcyclic` and calls the existing
`CategoryTheory.Sheaf.compact_basis_cofinal` and
`CategoryTheory.Sheaf.compact_cech_intersections` by their qualified names.
Those helpers were private. In their original, unclaimed module, removed only
their `private` modifiers and added short docstrings; their signatures, proofs,
and all other declarations and imports are unchanged. No theorem is duplicated.

The existing item node records this implementation of its elementary cofinality
and intersection steps. Its mathematical dependencies and unit route are retained.
Visibility change records:
`coord/changes/U6-public-compact-basis-cofinal.md` and
`coord/changes/U6-public-compact-cech-intersections.md`.

## Proved and sorry left

Closed the one original hole:
`TopCat.Sheaf.subsingleton_H'_of_quasiCompact_restriction_surjective`
(node `lem-sfb-quasi-compact-restriction-acyclicity`).

Holes closed: 1. Holes added: 0. Holes left in both delivered modules: 0.
Validation: `lcompile.py --all` compiled both modules cleanly: 2.9 seconds for
the existing helper module and 5.5 seconds for the item; exit code 0.
The two reused helpers and
`CategoryTheory.Sheaf.topological_filtered_injective_cech_acyclic` remain proved.
No decomposition or new statement is introduced. The item applies the existing
`TopCat.Sheaf.isZero_siteCech_of_surjective_unions` theorem as planned; its existing
hole is outside this delivery.

## No longer needed

Removed both duplicate helper declarations from the returned item, retaining
and reusing the originals. Removed the original direct proof import
`Sheaf.CategoryTheory.SiteCoveringAxioms`; its interface is available through
`Sheaf.Topology.CechVanishingSurjectiveUnions`. Added proof imports of that Čech
lemma, `Mathlib.Data.Fintype.Powerset`, and the existing compact-basis helper module.
No mathematical dependency, DAG node, or library module is pruned. All four
planned dependencies remain used. No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied two private helper proofs already present in
`Sheaf.Topology.FilteredInjectiveCechAcyclic`; the return correctly required reuse.
This packet exposes and imports the originals instead. Their module has no current
claim and had zero downstream importers. Declaration searches with
`tools/downstream.py --uses` found only that defining module; its internal calls
remain unchanged. The new proof import is cycle-free.

The implementation uses arbitrary finite index types rather than finite ordinals;
compactness supplies finite subtypes, giving the same cofinal collection of covers.
The mathematical statements and the unit route are unchanged.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
