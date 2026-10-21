## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardDirectImageUnitMorphismPullback.lean
from its coord/rework.tsv quarantine archive. Qualified the private helper's
single derivedPullback occurrence as AlgebraicGeometry.derivedPullback, fixing
its collision with the newer Scheme.Modules.derivedPullback. All other source,
including the public theorem signature, complete proof and imports, is preserved.
Updated only the existing node's Lean restoration metadata. The proof still uses
the two transpose comparisons, the single-pullback square, ordinary unit square
and tensor adjunctions specified by the DAG. The unit route is retained.

Change record: coord/changes/E3-picard-unit-morphism-pullback-restoration.md.

## Proved and sorry left

This assigned restoration has zero original holes: closed 0, added 0, remaining 0.
Restored the complete proof of
AlgebraicGeometry.Scheme.picardDirectImageUnitMorphism_pullback
(node lem-sc-picard-direct-image-unit-morphism-pullback) and its proved private
singlePullback_naturality helper. There are no split-off statements and no sorry
in the delivery. The repaired module compiles cleanly in 44.5 seconds. A separate validation
set recompiles it in 49.0 seconds, compiles the archived direct consumer
PicardDirectImageSectionMapRestriction unchanged in 28.7 seconds, and checks
#print axioms: only propext, Classical.choice and Quot.sound. These consumer and
axiom-check sources are scratch validation artifacts, not delivered modules.

## No longer needed

None. All archived imports and declared dependencies remain used. No node,
module, declaration or unit step is withdrawn. Search with LeanFinder, Loogle
and rg found the ordinary adjunction naturality ingredients already used in the
private helper, but no replacement for the specified canonical morphism theorem.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantined repair, rather than an unfinished proof.
The preserved helper predates Scheme.Modules.derivedPullback and its unqualified
name now selects the wrong functor. The original compiler error is a Type v
versus Type (v + 1) morphism mismatch. Explicitly qualifying the intended shared
functor repairs that error while preserving the public theorem exactly.
The archive, DAG attachment and parent dependencies are all retained.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
