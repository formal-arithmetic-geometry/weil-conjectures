## What changed

Retired `Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence`, a zero-hole
retire item. The upstream twin already supplies `finiteEtaleDescent_data` and
its capitalized `FiniteEtaleDescentCompatible` predicate. The old and upstream
predicates are definitionally identical (server-compiled `Iff.rfl` check).

Its only direct consumers, `Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective`
and `Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful`, now publicly
re-export their own upstream twins. These unclaimed modules have no downstream
importers. This also removes their duplicate theorem declarations. Updated the
three existing DAG Lean attachments to the upstream declarations. No source
library file, node statement, target, or unit route changed.

Change record: `coord/changes/retire-finite-etale-descent-data-existence.md`.

Server validation: both consumer modules compile independently without warnings.
A scratch check verifies predicate equivalence by reflexivity and prints the
axioms of the three upstream theorems; all use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Proved and sorry left

Actual item holes: zero before, zero after retirement. Closed 0 of 0 holes;
added 0 holes; split off 0. No `sorry` remains in delivered modules.
The existing complete upstream proofs of `AlgebraicGeometry.finiteEtaleDescent_data`,
`AlgebraicGeometry.finiteEtaleDescent_essSurj`, and
`AlgebraicGeometry.finiteEtaleDescent_fullyFaithful` are reused, with their
hypotheses and conclusions unchanged up to the definitionally identical predicate.
This is duplicate retirement, not a newly proved mathematical result.

## No longer needed

Deleted the duplicate module `Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence`.
Removed both public imports of it. In its essential-surjectivity consumer,
removed private imports of `WeilConjectures.AlgebraicGeometry.AffineFpqcDescent`,
`WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`, and
`WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover`: the proof is now supplied
by the upstream essential-surjectivity module, which retains its dependencies.
The retired item's direct imports of
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentData` and
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale` are supplied by
its upstream twin. No mathematical dependency node is pruned: the construction,
full-faithfulness and essential-surjectivity nodes all remain realized upstream.
The two consumer paths remain as re-exports for compatibility.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but this assignment is listed
as a retire item with zero holes in `coord/retire-items.tsv` and `coord/queue.tsv`.
The earlier DIFFERENT classification records only a renamed predicate and the
duplicate theorem; these do not require a second construction. The same
observation applies to its two consumer twins. Their bodies implement the
same arguments and their predicate hypotheses are definitionally identical.
The three node Lean attachments needed repointing; their mathematical statements
and proof dependencies were already correct.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
