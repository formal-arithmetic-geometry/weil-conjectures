## What changed

Proved `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
with its original signature. First construct a compactification of `u` from the graph in
an ambient compactification of `u ≫ f`, using quasi-compactness only of `u`. Identify
`Ru_!` with exact etale sum extension, compose its adjunction with the exceptional
adjunction for `f`, transport along unbounded compact-support composition, and apply
Mathlib `Adjunction.rightAdjointUniq`. Convert exact inverse image back to `Lu^*`.

Added three proof-only imports to the item: LowerShriekComposition,
EtaleCompactSupportGraphDerivedIso, and LowerShriek.EtaleMapProjection (the exact
sum-extension adjunction). Generalized the existing graph comparison API in
GraphGeometricBaseChange and GraphDerivedIso to arbitrary schemes. The first loses its
unnecessary Noetherian assumptions; invertibility and its inverse retain the necessary
`[QuasiCompact f]`. No graph, exchange, derived construction or core-data type changes.
Eta-expand the core comparison field to supply its original arguments to the broader API.
The change record lists all consumers of the broadened signatures; none needs a source
adaptation. The original geometric-point conservativity theorem is in
ProperProjectionFormula, which imports the assigned item and hence cannot be imported
by its graph-comparison prerequisite. Add the more general jointly-surjective derived
conservativity theorem, proved from the corresponding sheaf theorem and cohomology.
Use it for the family of algebraic-closure residue-field points. ProperProjectionFormula
itself stays unchanged. The original GraphCoherence, Normalization and
EtaleAmbientAdjointLocality consumers compiled against the generalized comparison API
without adaptation.

## Proved and sorry left

Closed one of the item's one holes:
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`.
The previously proved surjective-etale isomorphism-descent theorem stays proved.

The delivery adds zero holes and splits off zero theorems. One pre-existing hole remains
in an adapted dependency, with the same declaration name:
`AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange`
(`lem-asd-compact-support-graph-geometric-base-change`). Its hypotheses are generalized;
its graph-projection/mate-pasting proof in words already applies without Noetherianity.
The item therefore reduces to existing declared geometric obligations; this does not
claim that its full transitive axiom closure is sorry-free. Existing finite-graph support
normalization remains an imported obligation and is not changed by this delivery.

## No longer needed

GraphDerivedIso no longer imports Derived.Kunneth.ProperProjectionFormula. It imports
only the new, fully proved jointly-surjective conservativity prerequisite. No globally
reachable module is claimed pruned.
This proof does not use the simultaneous EtaleCompactSupportNormalization existence
statement, GraphCoherence, proper-refinement projection normalizations, or the normalized
unique-adjoint package in EtaleAmbientAdjointLocality. It only needs the explicitly
constructed graph comparison and the already proved unbounded composition theorem.
Thus those larger normalization/coherence obligations are not new dependencies of this
source theorem. The blueprint unit's Hom/adjunction route is retained.

Relative to the old marker `lem-amb-etale-adjoint-locality`, the direct dependency
`lem-asd-etale-compact-support-normalization` and the uniqueness/coherence work it
packages are unnecessary for this existence-only theorem. Common-refinement comparison,
proper/open interchange, open-extension composition and derived-pushforward composition
are used through the existing unbounded compact-support composition theorem, rather
than rebuilt or replaced by new obligations. Exact derived factorization and localization
are used through the graph-comparison API. Sheaf direct image, extension by zero and
sheafification remain underlying constructions, rather than globally pruned nodes.

## Where the brief, the DAG or earlier work was wrong

The assigned source module had no current `lean.module` attachment in the DAG. Its old
blueprint marker now points at a different, normalized Noetherian theorem in
EtaleAmbientAdjointLocality. Add an exact attachment for the existing arbitrary-scheme
source theorem instead of changing that separate theorem or its unit route.

The source-library unbounded compact-support composition theorem is stronger than the
bounded-below Noetherian comparison package recorded on the old blueprint node. Record
that already proved source theorem as an exact existing declaration; do not weaken the
assigned theorem or assume quasi-compactness of `f` or `u ≫ f`.

The J4 graph-comparison landing became visible during this session. Its finite-etale
case and data construction avoid a duplicate graph construction, but its unnecessary
Noetherian binders prevented reuse for the assigned theorem. The change record and both
statement-change records document their removal and check every DAG citer.

## New nodes

`lem-etale-exceptional-locality-arbitrary-schemes`: exact attachment and actual proof
route of the assigned source theorem.

`lem-etale-unbounded-compact-support-composition`: exact attachment of the already
proved source-library unbounded composition theorem. No new Lean statement or hole.

`lem-etale-derived-jointly-surjective-conservative`: jointly-surjective scheme pullbacks
detect isomorphisms in the unbounded etale derived category. This generalizes the existing
source geometric-point cohomology argument; it has a complete proof and no hole.

`lem-etale-sheaf-jointly-surjective-conservative`: exact attachment of the existing
source sheaf conservativity theorem for arbitrary scheme morphisms. The similarly named
blueprint etale-cover theorem is a narrower statement and cannot justify geometric-point
pullbacks. No new Lean statement or hole.

Validation: all four delivery modules compile; the original three comparison consumers
also compiled without adaptation.

Change record: `coord/changes/A2-etale-compact-support-arbitrary-base.md`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
