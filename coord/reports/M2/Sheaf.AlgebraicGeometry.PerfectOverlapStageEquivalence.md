## What changed

Repaired compilation performance in
`Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence`, preserving its four public
statements and all six canonical constructions re-exported from the adopted source.
The complete restored module initially exceeded the 60-second compile limit.

The restriction coherence proof now supplies its three existing equality-transport
proofs directly to `identityTransportCycle`, unfolding the large restriction
comparison once before simplifying, and avoiding repeated inference of the
intervening section objects. This tactic builds an application of that proved lemma;
Lean's kernel checks the resulting proof. The nested comparison normalizes module-category
aliases once. Local transparency settings keep the canonical comparisons, homotopy functors, and
localization functors abstract. The derived coherence application pins its functor
parameters explicitly instead of inferring them through the selected counits.
A private, explicitly typed `comparisonCounit` is exactly the existing canonical
`pinnedPullbackCounit`; the proved `comparisonCounit_isLeftDerived` supplies its
universal property. This keeps repeated selected-theorem expressions out of the
private coherence interfaces. No new counit is chosen. The source triangle removes
its identity comparison on components, and the concrete coherence application
unfolds its private aliases directly, avoiding simplifier proofs over whole
natural transformations.

The homotopy calculations use the representative already stored in each quotient
object instead of eliminating a surjectivity witness. The derived composition
factor uses the specific component lemmas and the identity law. A local priority
selects the preadditive structure from the same cached abelian structures.

The stage component equation is proved by whiskering the composition associativity
identity, combining equality transports at the natural-isomorphism level, and only then
taking the component. A private proof import of
`WeilConjectures.AlgebraicGeometry.PerfectHomTransport` reuses its proved `cc_assoc`.
The new private `isoTransport_trans_assoc` is proved by associativity and `eqToIso_trans`.
The node's proof steps and proof provenance record this calculation.
Change record: `coord/changes/M2-perfect-overlap-stage-proof-interface.md` lists the
local attributes, the definitionally identical private counit interfaces, and all
four current downstream modules. No consumer adaptation is needed.

## Proved and sorry left

The module retains complete proofs of
`AlgebraicGeometry.overlapOpenInclusionPullbackIso_whiskerLeft`,
`AlgebraicGeometry.overlapOpenInclusionPullbackIso_hom_comp`,
`AlgebraicGeometry.overlapOpenInclusionPullbackIso_inv_comp`, and
`AlgebraicGeometry.perfectOverlapStageObjectIso_hom_app`.
Every private helper is proved.

Validation: before the final restriction-unfold staging, the complete actual module
compiled without warnings in 57.3 seconds
through `lcompile.py`, with its compiled output written for the separate axiom probe.
The probe compiled and showed exactly `propext`, `Classical.choice`, and `Quot.sound`
for each of the four public theorems above. The final restriction-unfold staging
compiled through that proof in 13.0 seconds; delivery rechecks the complete file.
All four signatures match the current
published module verbatim. No library-wide build was run.

Starting holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
No theorem is split off, and no definition contains a proof hole.
This is a compilation repair, not a new hole closure.

## No longer needed

No imports, modules, or DAG dependencies are pruned. The same underived restriction,
pinned counit, localization, and composition dependencies remain necessary.
The stage proof no longer expands component maps to prove associativity, and
`overlapComposition_assoc` no longer re-extracts the full selected composition theorem:
it reuses the source library's existing proved associativity lemma.

## Where the brief, the DAG or earlier work was wrong

Q2 restored the quarantined adapter while this assignment was starting. The current
module therefore already had zero holes and used the canonical source constructions;
the remaining reproducible failure was the complete-file compile timeout.
No public statement, existing definition, target, unit route, or source-library
declaration is changed. Private counit interfaces use the definitionally identical alias.
The DAG dependencies are retained, with its final proof step describing the calculation
before component evaluation.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
