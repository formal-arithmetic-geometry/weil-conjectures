## What changed

Retire `Sheaf.RingTheory.CohenMacaulayDepthFirstTerm`, as assigned by
`coord/retire-items.tsv` and the human's retirement hand-off. `deleted.txt`
withdraws its file. Reattach node
`lem-weil-pbc-cm-local-free-resolution-mcm-depth` to
`WeilConjectures.RingTheory.CohenMacaulayDepthFirstTerm`, declaration
`IsLocalRing.first_term_depth_ge`. Its signature is byte-identical to the
copy's signature, including universes and all hypotheses; its proof follows
the same image-syzygy induction. The DAG statement and proof route stay intact.

No live Lean module imports the retired copy, so no consumer adaptation is
needed. The historical MCM consumer has moved upstream and already imports the
twin. The historical AuslanderBuchsbaum consumer is quarantined in
`coord/rework.tsv`; it is not a live source. The three extra public depth
helpers of the copy have no live users; upstream keeps its private helpers.
No upstream source or target statement changes.

Validation through `lcompile.py`: a scratch module importing the upstream
twin checks the theorem's type and prints its axioms; only `propext`,
`Classical.choice`, and `Quot.sound` occur. An unchanged sandbox copy of
`WeilConjectures.RingTheory.CohenMacaulayFreeResolutionMCM` compiles cleanly.
Both single-file checks finished in under two seconds each. A full live-source
import/name scan and `tools/downstream.py --uses` check consumer coverage.

Change record: `coord/changes/J3-retire-cohen-macaulay-depth-first-term.md`.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero holes left in
the withdrawn item. No split-off statements. `IsLocalRing.first_term_depth_ge`
is retained with its existing complete proof upstream. This is a retirement,
not a new proof or a decomposition.

## No longer needed

Pruned module: `Sheaf.RingTheory.CohenMacaulayDepthFirstTerm`.
Its redundant declarations `IsLocalRing.depth_equiv_local`,
`IsLocalRing.depth_subsingleton`, `IsLocalRing.depth_free_ge`, and private
`depth_kernel_ge` have no live external consumers. The main theorem remains
available upstream, so its node is preserved and reattached, not pruned.

Withdrawing the copy removes its five public imports:
`WeilConjectures.RingTheory.Depth`, `Mathlib.RingTheory.Noetherian.Defs`,
`Mathlib.LinearAlgebra.FreeModule.Basic`,
`Mathlib.Algebra.Category.ModuleCat.Basic`, and
`Mathlib.Algebra.Homology.ExactSequence`; and its four proof imports:
`WeilConjectures.RingTheory.DepthInSES`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`Mathlib.LinearAlgebra.FreeModule.Finite.Basic`, and
`Mathlib.RingTheory.Regular.Flat`.
These are still used by the upstream proof; no dependency node is claimed
unnecessary. No other module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but the current queue
assigns a zero-hole duplicate retirement. The retirement table's two historical
consumers no longer exist as live Sheaf sources. The DAG still pointed to the
redundant copy even though the unchanged theorem is already proved upstream.
The public helper visibility difference causes no live consumer failure.
No false mathematical statement or unit-route change was found.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
