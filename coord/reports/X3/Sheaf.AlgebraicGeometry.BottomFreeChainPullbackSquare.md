## What changed

Restored Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare from the quarantine
path recorded in coord/rework.tsv. Replaced its retired public import
Sheaf.AlgebraicGeometry.DerivedPullback with
WeilConjectures.AlgebraicGeometry.DerivedPullback. Kept the full theorem signature,
docstring, complete proof, finite-free comparison import and DAG dependencies.
The node proof_origin records the restoration. Change record:
coord/changes/X3-bottom-free-chain-pullback-square-restoration.md.

The explicit functor transports the two zero terms, two zero differentials and
invertible component. The existing bottomFreeChain_pullback_comparison supplies
the natural homology square. The module compiled without errors or warnings
through lcompile.py (23.3 seconds).

## Proved and sorry left

AlgebraicGeometry.Scheme.bottomFreeChain_pullback_square has a complete proof.
The quarantined module already had zero holes: 0 holes closed, 0 holes added,
0 holes left, 0 split off. This is restoration and import repair, not a new
hole closure. No new statements or definitions are introduced.

## No longer needed

The retired import Sheaf.AlgebraicGeometry.DerivedPullback is replaced by its
upstream provider. No mathematical dependency, node or module is pruned. The
quarantined parent ZeroBottomArrowPullbackLocal and its step-3 dependency on this
statement remain needed. No quarantined file is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole rework restoration, rather than an open proof obligation:
the archived proof is complete. Its old derived-pullback import became invalid
after sync. The restored comparison theorem fits the existing proof unchanged.
The unit route and mathematical statement need no correction.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
