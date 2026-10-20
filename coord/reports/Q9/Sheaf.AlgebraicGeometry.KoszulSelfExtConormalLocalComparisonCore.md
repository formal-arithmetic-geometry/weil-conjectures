## What changed

Retired Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore, the duplicate
listed in coord/retire-items.tsv. Its theorem was already proved in the current
source. Reused the proved theorem from the corresponding WeilConjectures module.
The only direct consumer, Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison,
now imports that theorem privately and rewrites exteriorPower to exteriorSheaf
using the existing proved exteriorSheaf_eq_exteriorPower. Its public imports,
statement, visibility, docstring, and remaining proof are unchanged.

Updated new-w4-koszul-self-ext-local-iso to the existing upstream declaration and
its actual frame dependencies. Updated its sole DAG parent's proof to record the
exterior-construction transport. The unit route is preserved. The change record is
coord/changes/Q9-retire-koszul-self-ext-local-comparison-core.md.

Validation: the original assigned module and the adapted consumer both compile
through lcompile.py. Import-direction checking accepts the upstream import. A
current source-graph comparison shows that the new consumer closure adds only the
upstream core, whose dependencies were all already present. The unconditional
exterior equality preserves empty-open and all-degree cases. The delivery dry run
passed preflight (CODEX review class). Its automatic axiom probe timed out, so a
separate direct #print axioms check was run through lcompile.py; it compiled in
2.1 seconds and confirmed that the upstream local-isomorphism theorem and the
adapted consumer both use only propext, Classical.choice, and Quot.sound.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in any delivered Lean file. This is a duplicate retirement,
not a new proof or a decomposition.

AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_iso remains
available from its already proved upstream module, with the same mathematical
meaning by exteriorSheaf_eq_exteriorPower. The consumer theorem
AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_comparison retains
a complete proof. Direct axiom checks of both declarations contain no sorryAx
or any axiom beyond propext, Classical.choice, and Quot.sound.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore.
Removed its private import from the sole direct consumer. The duplicate private
restrictLocalFrame construction is no longer needed; the upstream construction
carries the same argument. No source-library declaration is removed.

The four frame/basis dependencies of new-w4-koszul-self-ext-local-iso remain needed
by the upstream proof. The exterior-construction equality is no longer a proof
dependency of that upstream core; it is needed by the legacy consumer and is
recorded on the parent's node instead. No mathematical node is deleted or bypassed.
No further module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished obligation split nine times,
but the current assigned source already contains a complete proof and no holes.
The applicable concrete work is its listed retirement. The old retirement note
PROOFDIFF_UNSAFE describes an earlier dependency graph: the current consumer
already imports every dependency of the upstream core. The only new upstream
module is the core itself, replacing the withdrawn duplicate.

The upstream theorem uses exteriorPower; replacing its import alone would leave
a source-type mismatch with the unchanged legacy consumer. The existing proved
exteriorSheaf_eq_exteriorPower supplies exactly the required transport. This
retirement preserves the actual local-existence argument and the parent's
separate overlap-alignment dependency.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
