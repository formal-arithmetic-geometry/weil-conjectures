## What changed

Restored `Sheaf.Paper.FiniteCoefficientDirectImage` from its preserved quarantine
source for the assigned global-build repair. The archive contained no holes.
The original compiler fails while elaborating pro-etale scalar functors with
`u + 1 =?= max (u + 1) ?u` for `EssentiallySmall X.ProEt`.
A compiler instance-search trace identifies `WeilConjectures.scalarReductionSiteSmall`
as the selected instance with the unresolved auxiliary universe.
Disable that instance while elaborating this file, then restore its instance
attribute at the end for consumers. The standard site-size instance supplies
the fixed universe instead. Every existing declaration, proof, import and
mathematical construction is preserved verbatim.

The initial pro-etale block and the full restored module compile through
`lcompile.py`; the full module took 45.3 seconds, below the 60-second limit.
The delivery command performs the final server compile and preflight checks.
Change record: `coord/changes/S2-finite-coefficient-direct-image-site-size.md`.

## Proved and sorry left

Holes before repair: 0. Holes closed: 0. Holes added: 0.
Holes left in the restored item: 0. No statements were split off.
This is a compatibility restoration of an already proved module, not a new claim
of closing its historical six holes. Existing dependency holes are unchanged.

## No longer needed

None. No import, declaration, node, module, or proof dependency is removed.
The node's existing proof route and Lean attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

The queue entry is a repair, not an unproved item. Its source is absent from
`lean/` because it was quarantined after a failed global build; the preserved
2147-line archive already contains full proofs. Zero live importers does not
make it unused: fifteen archived direct consumers still require its interface.
No mathematical defect in the node's statement or proof route was found.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
