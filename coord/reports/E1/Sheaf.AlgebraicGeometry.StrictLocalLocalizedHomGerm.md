## What changed

Completed the retirement listed in coord/queue.tsv and coord/retire-items.tsv.
Withdraw the empty-of-declarations Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm
re-export, and change the sole live consumer,
Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm, to import
WeilConjectures.AlgebraicGeometry.StrictLocalLocalizedHomGerm directly. This is
exactly the provider its old import re-exported. No declaration changes.

The node lem-weil-pbc-strict-local-localized-hom-germ keeps its existing SmallModel
Lean attachment, statement, dependencies and proof; only lean.note records the
retirement audit. Its quarantined original-model implementation is preserved.
Change record: coord/changes/E1-retire-strict-local-localized-hom-germ.md.

The adapted consumer compiles through lcompile.py (3.2 s). Search used msearch.py
LeanFinder, Loogle and grep, plus direct source and DAG scans. The existing upstream
proof supplies the canonical comparison; there is no reason to reprove it here.

## Proved and sorry left

Item: zero original holes; zero holes closed; zero holes added; zero split off.
This is a retirement, not a new proof or a decomposition.
The adapted consumer retains exactly its pre-existing hole
AlgebraicGeometry.Etale.closedFibre_unit_stalk_comparison
(lem-weil-pbc-local-acyclicity-closed-fibre-ordinary-germ); its theorem and proof
are unchanged. No other delivered Lean declaration has a hole.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm.
Removed the live consumer's private import of that wrapper and replaced it by the
upstream import. No mathematical node or dependency is pruned. The upstream proof
and its proof imports remain. The original-model SmallModel realization and all
five DAG parents remain, including quarantined ones. No quarantine archive is
edited or listed in deleted.txt. The historical StrictLocalUnderivedSectionsMate
consumer already uses its upstream provider; the archived unprefixed
StrictLocalComplexSectionsMate remains separate rework, with its current SmallModel
replacement and DAG attachment preserved. The change record lists every downstream
module and the relevant archived consumers.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with a sorry or definition repair, but
the current source is already a zero-declaration upstream re-export and the queue
explicitly assigns retirement. The historical retire inventory describes an older
conflicting definition implementation and lists three historical consumers; the
current library has only one live direct importer. The current DAG attachment is
the separate, quarantined small-colimit-model implementation. Moving that attachment
to the canonical strictLocalization theorem would change its objects; this packet
preserves it and all parent dependencies. No target or source-library file changes.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
