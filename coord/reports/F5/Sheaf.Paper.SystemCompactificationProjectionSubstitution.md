## What changed

Proved `WeilConjectures.SystemTensorMate.refinementDirectId_existsUnique` from
Mathlib's continuous module pushforward isomorphisms and the existing
constant-section uniqueness theorem. The inverse base-change identity gives the
specified section formula; sectionwise extensionality gives uniqueness.
All existing signatures and definitions are unchanged.

## Proved and sorry left

Closed one of four original holes:
`WeilConjectures.SystemTensorMate.refinementDirectId_existsUnique`.
Added zero holes. Three original holes remain, all on
`lem-pur-system-compactification-pf-substitution`:

- `WeilConjectures.SystemTensorMate.refinementGamma_isIso`.
- `WeilConjectures.SystemTensorMate.system_compactification_pf_substitution`.
- `WeilConjectures.SystemTensorMate.system_compactification_refinement_coherence`.

This is a partial proof, with no decomposition or new nodes.

## No longer needed

None. The original proof-dependency imports are retained for the three unfinished
original theorems; the proved identity uses the existing public imports.

## Where the brief, the DAG or earlier work was wrong

The earlier missing published `RefinementCategory` object is now available.
The retained identity draft needed explicit functor arguments for the continuous
pushforward API, and dependent elimination of the sequence-site object in the
uniqueness proof. These repairs avoid expensive functor inference and preserve
both the statement and its prescribed section normalization.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
