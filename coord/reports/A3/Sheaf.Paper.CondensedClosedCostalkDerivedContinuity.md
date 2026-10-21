## What changed

Restored Sheaf.Paper.CondensedClosedCostalkDerivedContinuity from its assigned
quarantine archive, retaining both public theorems and every original dependency.
Named the recollement existential proofs before unpacking their dependent witnesses.
Added file-local irreducibility for CategoryTheory.Mod.monoidalClosed and
AlgebraicGeometry.ProEtale.upperStarFromPoint to use their existing APIs without
unfolding their implementations. All signatures, definition bodies, private helper
interfaces, and exported attributes remain unchanged.

The complete module compiled without errors or warnings in 34.8 seconds.
The change record is
coord/changes/A3-restore-condensed-closed-costalk-derived-continuity.md.

## Proved and sorry left

This is a source restoration and elaboration repair, with zero original holes.
The restored complete proofs are
AlgebraicGeometry.ProEtale.colimit_isStrictlyGE and
AlgebraicGeometry.ProEtale.condensed_closed_costalk_derived_continuity
(node lem-weil-pbc-condensed-closed-costalk-derived-continuity).
Holes closed: none. Holes added: none. Sorry left in the item: none.
No statements are split off and no new modules are introduced.

## No longer needed

None. All four original imports remain: the continuity cocone and qcqs comparison,
open/closed recollement, exact degreewise colimits, and pointwise short-complex
exactness are used by the proof. Both existing proof-dependency nodes remain needed.
The existing DAG proof already records exactly the restored argument, so no node
update is required. No module is withdrawn or pruned and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The live source is missing because of the recorded cluster-restore reversion;
it is not an unused or withdrawn theorem. The preserved proof contains zero sorries.
Its direct obtain and rcases operations fail with
`Tactic generalize failed: result is not type correct` against the current imports.
Naming the existential proofs before unpacking them avoids those failures. The final
local elaboration settings preserve the mathematical statements and proof route.

The shorter-route search found the existing Mathlib five lemma, already used in
the restored private triangleComparison_isIso helper. LeanFinder returned general
derived-category factorization lemmas, and the Mathlib grep returned only the
generic pointwise-right-derived colimit API; neither replaces closed-costalk
continuity. Library searches found no duplicate of either public theorem.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
