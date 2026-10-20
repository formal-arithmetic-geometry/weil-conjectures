## What changed

Completed the assigned retirement row in `coord/retire-items.tsv`. Withdrew
`Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives` using `deleted.txt`.
Its sole direct consumer, `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData`,
now privately imports the proved upstream twin. All consumer declarations and
proofs stay verbatim. Redirected node
`lem-sc-proj-twist-finite-local-representatives` to the upstream module, file, and
verbatim signature. The node's mathematical statement and proof dependencies stay.

Change record:
`coord/changes/G2-retire-proj-twist-finite-local-representatives.md`.

The original theorem and upstream twin agree verbatim after renaming only the
unused existential span-proof binder `hspan` to `_`. Both combine the same finite
values theorem with canonical evaluation. The unit record
`sk-thm-picard-duality` has no realized step at this level. The existing node stays
attached to the same declaration upstream, so no mathematical dependency is
withdrawn or bypassed. No upstream file or target changes.

The changed consumer compiled without warnings. The import-direction check
accepts the import. The downstream scan finds only that consumer, and its source
import closure has no nonempty Sheaf/upstream twin pair. A separate axiom probe
checks both `twist_finiteLocal_representatives` and `twist_finiteLocalization_data`.
Both use only `propext`, `Classical.choice`, and `Quot.sound`; neither uses
`sorryAx`. The temporary probe was removed before delivery.

Searches through `msearch.py` covered LeanFinder, Loogle, and Mathlib grep.
LeanFinder found related Proj structure-sheaf fraction declarations; Loogle and
grep found no exact named statement. Direct library search found the exact proved
upstream twin, used here instead of reconstructing the proof.

## Proved and sorry left

The assigned module has zero holes. Closed zero holes and added zero holes;
split off zero statements. No delivered Lean file contains a `sorry`. This is
retirement of a proved duplicate, not a new theorem proof claim. The preserved
upstream declaration is `AlgebraicGeometry.Proj.twist_finiteLocal_representatives`;
the unchanged consumer theorem is
`AlgebraicGeometry.Proj.twist_finiteLocalization_data`.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalRepresentatives` and removed
its sole import from `Sheaf.AlgebraicGeometry.ProjTwistFiniteLocalizationData`,
replacing it with the existing upstream twin. The duplicate's imports and theorem
are no longer compiled. No mathematical node, lemma, proof dependency, or unit
step is pruned: the original node now points upstream. No other module is
withdrawn, and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split open proof. The current queue and
retirement inventory instead assign a proved duplicate with zero holes. The
concrete repair is the consumer import migration, withdrawal, and DAG attachment
redirect. The inventory's DIFFERENT classification reflects layout, a lint option,
and the unused existential binder name, rather than different mathematics.
No mathematical statement was disputed and no new node was needed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
