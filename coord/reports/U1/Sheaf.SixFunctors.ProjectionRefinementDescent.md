## What changed

Restored the assigned quarantined module and retained the complete finite-descent
assertion and already-proved intrinsic-system specialization. The finite clause uses
`coefficientProjectionComponent`, the exact component of the existing
`finiteProjection` spelling of `projectionMapOfCompactification`, with unchanged
hypotheses and conclusions. Replaced the finite
hole by a Lean assembly of the domain, single-refinement, coherent-comparison and
common-refinement descent arguments. The descended transformation is the actual
projection transformation at the chosen base compactification, restricted to the
full input category; its comparison equation is proved by two refinement squares
and cancellation of comparison isomorphisms, without inverting any projection.

Moved the original ten fixed-scalar constructions into the new public
`ProjectionRefinementData` module, publicly reexported by the item. Three generic
coefficient abbreviations package the same native image and projection bifunctors;
`image`, `source` and `target` specialize these abbreviations. `refinementLaw` uses
`coefficientProjectionComponent`, whose body is the exact native projection through
`finiteProjection` and whose tensor endpoints are declared explicitly. The new
`ProjectionRefinementInputs` proof uses the proved finite-ring origin theorem and
`CompactSupportFiniteProjection.domains`, then transports through the canonical
coefficient and pullback comparisons. `ProjectionRefinementComparisons` extends
the existing coherent origin-category comparisons by Mathlib's essential-image
lift; full faithfulness proves normalization for every presentation.
`ProjectionRefinementSquare` uses the proved directed `refinementProjectionCounit`
and cancels the inverse comparison pairs. Its only new mathematical input is the
strictly smaller normalization statement in `ProjectionRefinementNormalization`.

Generic coefficient packaging and explicit component endpoints fix the categorical
instances before substituting the concrete coefficient quotient. This follows the documented `finiteProjection`
API in `RefinementProjectionCounit` and removes slow instance diamonds between
concrete native maps and generic proper/open wrappers. The two cancellation
identities and the restricted transformation's component formula are proved
privately over a generic coefficient ring and then specialized; all retain the
native maps. Exported transparency is
unchanged; the change record lists the definitionally equal spellings explicitly.

No existing module besides the item is edited. A fresh direct-import search found the newly available consumer
`Sheaf.Paper.FiniteProjectionFromDescent`; it is checked unchanged against this packet. The target
statements and the unit's compactification-independence route are retained.

## Proved and sorry left

Original holes: one,
`WeilConjectures.ProjectionRefinementDescent.finite_descent`. Its body is now a
complete proof from the named arguments below. The already-proved
`WeilConjectures.IntegralSystemRealization.projectionRefinementSystems` is preserved.

New proved public theorems:

- `WeilConjectures.ProjectionRefinementDescent.tensor_and_origins`.
- `WeilConjectures.ProjectionRefinementDescent.comparison_cocycle`.
- `WeilConjectures.ProjectionRefinementDescent.refinement_square`.

Exactly one hole is added:
`WeilConjectures.ProjectionRefinementDescent.normalized_refinement_inverse`, node
`lem-sf-projection-refinement-normalization`. This identifies the inverse of a
witnessed refinement comparison with the canonical directed proper/open mate and
its conjugate direct-image compositor. It mentions no tensor, projection map,
constructibility, Tor amplitude, natural descent family or descended transformation.
The new docstring states the site-transport, identity normalization, witness
naturality and conjugate-compositor argument in full. Thus the delivery closes
one upper hole and adds one strictly smaller hole: a decomposition, net zero
holes closed among this packet's declarations. Closure counts are left to the
project ledger. There are no holes in definitions or private helpers.

Validation: all six intended modules compiled on the project server. The completed
item compiled in 14.6 s, including 1.21 s of tactic execution and 0.283 s of kernel
type checking under the diagnostic profiler. The direct consumer
`Sheaf.Paper.FiniteProjectionFromDescent` compiled unchanged in 58.0 s against the
packet; its copy was byte-checked against current shared source and removed. All
temporary probes and profiling options were removed. Delivery preflight checks
the final packet again. Both delivery attempts reached the push step after
server preflight, but remote Git rejected both with `remote unpack failed: unable
to create temporary object directory`. No delivery was accepted. The compiled
packet is preserved for retry after the server is repaired.

## No longer needed

The old direct proof imports below are removed from the item. They are not
withdrawn from the library, and some remain needed transitively by existing APIs:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.EtaleTorFlatPullbackModel`
- `Sheaf.Algebra.Homology.BoundedOneSidedTensorRealization`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`
- `Sheaf.Paper.FiniteTensorConstructibleCohomology`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`
- `Sheaf.Paper.ProEtaleProperOpenComparison`
- `Sheaf.Paper.ProperOpenComparison`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Paper.RingedProjectionTensorComposition`

The explicit domain-model route is unnecessary here: its first eight modules are
replaced by the already-proved projection-domain and finite-ring-origin results.
The explicit local/outer projection pasting is replaced by the proved
`refinementProjectionCounit`. The site-normalization dependencies remain in the
new normalization node's proof plan; no global claim of their irrelevance is made.
The origin-category coherence remains necessary in the proved comparison module.
All original public imports are retained through the data module. The data module
additionally publicly imports `RefinementProjectionCounit` because `refinementLaw`
uses the exact component of its `finiteProjection` definition.

Removed obsolete direct `tool_uses` approvals from the original node for
`lem-sf-proetale-constructible-origin`, `lem-sf-comparison-tor-amplitude`,
`lem-sf-etale-tor-flat-pullback-model`, `lem-sf-bounded-one-sided-tensor-realization`,
`lem-weil-pbc-comparison-pullback`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-pullback-preserves-bounded-constructible`,
`lem-pur-finite-tensor-constructible-cohomology`,
`lem-sf-open-tensor-normalization`, `lem-sfb-ringed-projection-tensor-composition`,
`lem-sf-proper-open-comparison-site-normalization`,
`lem-weil-pbc-proper-open-comparison-proetale`,
`lem-cbc-proper-open-interchange-coherence`, and
`lem-cbc-strict-tower-proper-open-calculus`. Their existing declarations are neither
removed nor weakened. No module is withdrawn and no source-library declaration
is changed.

## Where the brief, the DAG or earlier work was wrong

The original detailed plan is mathematically consistent but longer than the
available library route. Its domain construction and projection pasting are
already packaged by proved declarations. The subtle remaining issue is equality
of the retained-witness comparison with the directed mate, including the precise
canonical compositor; invertibility alone would not suffice. This is the sole
split-off hole, rather than another copy of the full projection-descent statement.

The source was absent because it was quarantined, not because it was unused. The
packet preserves its source declarations, Lean attachment, statement and unit route;
the assigned module is restored rather than withdrawn. No statement
is disputed, no extra finite-Tor condition is imposed on K, and no absolute
separatedness assumption is added to either scheme.

A read-only DAG audit encountered an existing cycle outside this packet:
`prop-nagata-relative-proj-functoriality` → `lemma-nagata-relative-proj-exists` →
`lem-nagata-proj-affine-restriction` → `lem-nagata-affine-proj-scalar-extension` →
`prop-nagata-relative-proj-functoriality`. This is reported for the maintainer; those
nodes are untouched. A separate reachability check confirms that no dependency
returns to any of the six nodes changed or added by this packet.

The delivery tool failed at the Git server on both attempts (2026-10-26 UTC):
`remote unpack failed: unable to create temporary object directory`. This is a
server unpack failure after preflight, not a Lean compile failure. The launcher
scripts and server repository were not edited or bypassed.

## New nodes

`def-sf-projection-refinement-domains` attaches the ten fixed-scalar constructions,
the three generic coefficient abbreviations, and the explicitly typed projection
component to their new data module. The constructions are definitionally unchanged; projection formulas use the existing
`finiteProjection` wrapper around the exact native map and its evaluated component. Change record:
`coord/changes/U1-projection-refinement-data.md`.

`lem-sf-projection-refinement-inputs` states and proves origin existence and tensor
domain closure, using the supplied operation datum and proved intrinsic domains.

`lem-sf-projection-refinement-comparisons` states and proves the natural coherent
comparison family, normalized on every common refinement and every retained origin.

`lem-sf-projection-refinement-square` states and proves the single-refinement
projection square from the existing directed square and the normalization lemma.

`lem-sf-projection-refinement-normalization` is the one remaining hole: equality of
the witnessed inverse comparison and the canonical directed proper/open mate,
including its direct-image compositor. It is independent of the tensor and
projection-formula equations that use it.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
