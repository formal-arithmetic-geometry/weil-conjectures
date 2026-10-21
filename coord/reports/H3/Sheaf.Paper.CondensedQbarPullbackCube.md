## What changed

Removed the unused private qbarPull_square_cube calculation from the restored item.
The public theorem already uses qbarPull_square_cube_iso directly through the
abstract coefficientCube_of_iso, so elaborating and kernel-checking a second
concrete hom-component equation is redundant. Every remaining proof, public
signature, import, definition and reducibility setting is retained. The node's
proof and proof_origin now describe this pruning. The change record is
coord/changes/H3-qbar-cube-unused-hom-calculation.md.

## Proved and sorry left

This assigned rework starts with zero textual sorry occurrences and ends with
zero. Holes closed: none (0 of 0). Holes added: none. Split off: none.
The completed proofs of coefficientCube_of_iso, qbarPullIso_comp, qbarPull_eq,
qbarPull_square_cube_iso and constructibleToQbar_pullback_cube are retained.
No theorem or definition is added and no other module is modified.

## No longer needed

The private qbarPull_square_cube helper is removed; no proof calls it. The public
cube uses the isomorphism equation directly. Searches of both live library roots
and quarantined sources find no caller and no import-all consumer of this module.
No imports, nodes or modules are pruned. Both private imports remain necessary:
ContinuousIntegralPullComposition supplies derived_pull_comp and bounded_comp_hom;
ContinuousIntegralExchangeTargetAdjunct supplies mapped_iso_rectangle and
inverse_mapped_square. The quarantined CondensedQbarExchangeLeftAdjunct still
applies the public cube, so the module and its node remain needed. The unit route
and every mathematical dependency are preserved.

## Where the brief, the DAG or earlier work was wrong

The historical E1 sandbox named in the handoff does not exist here. The current
live module was already restored by J7 with every original hole closed and the
obsolete identifier repaired. H3 began with dispatcher metadata only and copied
that current module, preserving the completed proof. This is therefore a zero-hole
proof-cost repair, not a new five-hole proof. The unchanged file compiled cleanly
in 53.4 seconds, leaving little margin under the 60-second limit.
Profiling located repeated concrete derived-functor comparisons. Broader rewrites,
direct final equation normalization, and folding the bounded pullback functor
were tested and discarded because they were slower or disrupted the focused
component calculation. The delivered change retains the working composition
proof and removes only the unused concrete hom-component calculation.
The downstream query reports no live importers; the quarantined direct consumer
at line 376 and the DAG still require the public theorem. No withdrawal is claimed.
Searches through msearch.py returned generic underived sheaf pullback composition
and functor mapIso laws, with no shorter specialized derived Qbar cube theorem.
The required delivery command performs final compilation, preflight and axiom
checks. No second-reading section is supplied, as required by the dispatch brief.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
