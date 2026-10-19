## What changed

Proved AlgebraicGeometry.Scheme.pbcDescentFunctors with its statement unchanged.
The proof uses the existing quotient functor and representative formula. Private,
fully proved helpers establish additivity at a common stage, construct the descended
shift comparison from Morphism.Hom and descNatTrans, verify its zero/addition laws,
and show that ιCompFunctorIso commutes with shifts. Exactness follows by representing
a distinguished triangle as an included stage triangle and using exactness there.
The remaining transformation formulas and equations use the upstream API directly.
Updated the node's exactness step and proof dependencies to record the use of the
common-stage Verdier criterion. No public definition or signature changed.
Change record: coord/changes/C2-pbc-descent-private-proof-context.md.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.pbcDescentFunctors
(node prop-weil-pbc-descent-functors).

Remaining: AlgebraicGeometry.Scheme.pbcDescentOperations
(node prop-weil-pbc-descent-functors), unchanged. This still requires constructing
the four coherent operation families from the normalized rational scalar mates,
proving their canonical BetaSpec clauses and exchange compatibility, and applying
the now-proved general descent theorem.

Initial holes: 2. Closed: 1. Added: 0. Remaining: 1.
All private helpers are proved; no new assumed statement or arbitrary choice was added.

## No longer needed

The scalar-extension, pair-category, common-stage calculus, common-stage cones,
Qbar-category and rational-transport nodes are retained: the first theorem uses their
canonical structures, and the operation application still needs rational transport.
Removed the unused proof import Sheaf.Paper.IntrinsicQbarCategory. The general
descent uses the Qbar pair category directly, so it needs no intrinsic-category
comparison or envelope. No unit statement or route is bypassed. No module is
withdrawn and no import is added.

## Where the brief, the DAG or earlier work was wrong

The assigned file was initially absent during shared-snapshot synchronization and
subsequently appeared; work started from that complete published source.
The general descent proof needs the explicit common-stage distinguished-triangle
criterion supplied by the Verdier theorem. Its dependency is now recorded.
The node thm-weil-pbc-verdier-axioms is used as a tool: its exact stage
inclusions and distinguished-triangle criterion justify exactness on the
already supplied pair-category triangulation. This replaces no unit step;
the descent node retains its stagewise construction and transformation proof.
Concrete-category elaboration initially exhausted the default heartbeat budget;
the generic stage-system proofs avoid unfolding the coefficient constructions.
No statement correction was needed.

Validation: after resuming the interrupted session, the complete delivered module
compiles against the current published build through lcompile.py in 11.9 seconds,
with no errors or warnings. The first preflight also compiled the module and found
only a missing change-record path in this report; that path is now recorded above.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
