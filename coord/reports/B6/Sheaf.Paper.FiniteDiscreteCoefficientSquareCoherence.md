## What changed

Restored Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence from its quarantine archive.
In its private etale_square_eq proof, replaced the removed upstream equation lemma
Etale.pullbackSquareComparison_def with direct unfolding of Etale.pullbackSquareComparison.
All signatures, constructions, imports, and the rest of the archived proof are preserved.
The existing node's proof-origin note records this API repair; its Lean attachment and
dependencies are preserved. Change record:
coord/changes/B6-finite-discrete-square-coherence-sync-restoration.md.

The proof still uses ordinary composition coherence, transports it through exact
derivation, D+ restriction and left-derived replacement, and obtains square coherence by
categorical cancellation. No new mathematical statement or split is introduced.

## Proved and sorry left

This is the assigned repair of a zero-hole module: 0 holes before, 0 holes closed,
0 holes added, 0 holes remaining, and 0 split off. The complete proof of
AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientPullbackIso_square
is retained, with the repaired private normalization proof. Its node is
lem-weil-pbc-finite-discrete-coefficient-square-coherence.

Remote validation: the restored module compiled in 24.9 seconds, and the unchanged
archived direct consumer FiniteDiscreteCoefficientCoherentPullbacks compiled in
4.6 seconds against it. The axiom probe reports propext, Classical.choice, Quot.sound
and inherited sorryAx from the existing dependency closure. The restored item has
no local sorry and introduces no axiom.

## No longer needed

The obsolete reference to Etale.pullbackSquareComparison_def is removed. No imports,
nodes or modules are pruned. Every declared proof dependency remains needed. Searches
using LeanFinder, Loogle and repository rg found generic natural-isomorphism composition
facts, but no replacement for the complete coefficient-coherence argument.

## Where the brief, the DAG or earlier work was wrong

The archive still referenced an equation lemma removed by the upstream sync, as recorded
in coord/rework.tsv. The underlying definition and mathematical argument are unchanged;
direct unfolding supplies the same equation. There is no statement dispute or change to
the unit route. The first remote compile request received no answer from the busy server
within its request window; this is retried under the brief's busy-server instructions.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
