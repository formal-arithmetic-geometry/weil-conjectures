## What changed

Prove `WeilConjectures.ProjectionCoefficient.concreteProjectionFieldDescent` without
changing its theorem signature. Preserve the endpoint maps through the proved
component-formula identities and the tensor predicate through an equivalent
representation. Use the supplied
`SixFunctorExchangeComparison.projection` square directly: postcompose with the
last endpoint isomorphism and cancel the first one. This proves the rational,
finite-extension and common-stage transport equalities uniformly.

Private proved helpers establish preservation of scalar identity/tower and
inclusion equations by composition and Cartesian products. Apply these helpers
to support × identity followed by tensor (source), and identity × pullback,
tensor, then support (target). The operation datum supplies support/pullback
coherence and the existing `TensorCoherence` hypothesis supplies tensor coherence.
Uncurrying the supplied projection transformation gives naturality for arbitrary
arrows, including rational and common-stage arrows. Its naturality at transition
isomorphisms gives enlargement independence. Functoriality and cancellation of
endpoint isomorphisms give the inverse and forward-equality clauses.

Repair `ProjectionTensorCoefficientCocycles.TensorCoherence` to group its existing
identity and tower equations in `ExchangeProjectionScalarCocycle`. This is an
equivalent predicate; the common-stage inclusion equation is retained. The only
consumer is this item. Normalize `endpoint` with the existing coefficient aliases;
use Bool matches for `endpoint` and `commonEndpoint`, retaining the same branches,
parenthesize the target as its two-step composition, and express
`sourceIso`/`targetIso` as components of natural composites. `EndpointCocycles`
stores the source and target scalar-cocycle structures, whose identity and tower
fields expand to the old Bool-indexed equations. This changes only the
representation of the same predicate. The proved
private lemmas `sourceIso_formula` and `targetIso_formula` identify these maps with
the original ordered component formulas. These representation repairs avoid
expanding the concrete localization category during proof checking. All existing
theorem signatures and public imports are retained; no module held by another
group is adapted, and no new node is introduced.

The change record is
`coord/changes/projection-field-descent-coherence-interface.md`. The existing
predicate node records the equivalent representation repair. Its mathematical
statement is unchanged, including identity extensions and arbitrary towers.
The target meanings are unchanged.

## Proved and sorry left

Close the single hole in
`WeilConjectures.ProjectionCoefficient.concreteProjectionFieldDescent`
(node `lem-sf-concrete-projection-field-descent`). Holes closed: 1; holes added: 0;
holes left in the delivered module: 0. The repaired tensor-predicate module also
contains 0 holes. All private helpers are proved.
The proof uses the supplied operation datum; it does not assert that all
transitive dependencies are already axiom-free.

## No longer needed

Remove these proof imports from this module:

- `Sheaf.Paper.ConcreteIntegralProjectionCone`
- `Sheaf.Paper.CompactificationCompletedRealization`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.ScalarExtensionTowerCoherence`
- `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Paper.CompletedOpenTensorSystemRealization`
- `Sheaf.Paper.CoefficientRealizationTransport`
- `Sheaf.Paper.SfScalarExtensionComposition`
- `Sheaf.Paper.PbcScalarExtension`

These correspond to the old proof dependencies
`lem-sf-concrete-integral-projection-cone`,
`lem-fix-compactification-completed-realization`,
`lem-weil-finite-free-completed-scalar-comparison`,
`lem-weil-integral-scalar-extension-constructible`,
`lem-pur-integral-operations-scalar-extension`,
`lem-pur-scalar-extension-tower-coherence`,
`lem-pur-ordinary-adjunction-scalar-compatibility`,
`lem-sf-open-tensor-normalization`,
`lem-pur-completed-open-tensor-system-realization`,
`lem-sf-pf-coefficient-realization-transport`,
`lem-weil-scalar-extension-composition`, and `prop-weil-pbc-scalar-extension`.
The supplied datum already includes the comparison squares that the former plan
would reconstruct from primitive models, so none is needed by this proof.
Remove the corresponding obsolete top-level `tool_uses` entries in the item node.
The definition nodes `def-exchange-projection`,
`def-weil-rationalization-karoubi`, and
`def-weil-algebraically-closed-coefficients` remain statement dependencies through
the unchanged public imports; they need no separate proof step here.

No module or declaration is withdrawn. Other consumers may still need any of
these modules; the delivery claims only that this item's proof no longer uses them.
The unit `sk-rem-sf-pf-done` has no realized statement or proof steps, and its
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The older plan reconstructs coefficient compatibility from primitive completed
models, although `SixFunctorExchangeComparison` already records precisely the
projection square needed by this theorem. Its scalar and inclusion cocycles are
also directly available in `SixFunctorCommonStageCoherence` and the theorem's
existing `TensorCoherence` hypothesis. The shorter proof uses these supplied
interfaces, with no projection-invertibility assumption.

The resumed sandbox contained a proof draft. Its original signature was checked
against the current source. The draft was not treated as verified input: repeated
compiles exposed excessive unfolding in the tensor-coherence adapter. In particular,
the raw `rationalTensor` uses `ScalarLocalization.category`, while the operation
comparison uses the cached `stageCategory`; checking the component adapter repeatedly
expanded their Hom and composition implementations and hit the per-file limit.
Reusing the existing scalar-cocycle structure (also suggested in the stage-2 node
review) removes that adapter. Factoring endpoint isomorphisms through natural
composites removes the same conversion pressure in the endpoint calculations.
The private component-formula proofs verify that the specified maps are preserved.
The original expanded endpoint predicate also forced the kernel to unfold the
concrete category when checking the assembled proof. Storing the same source and
target scalar-cocycle structures avoids this conversion: the entire item compiled
in 24.7 seconds, with every proof complete. Profiling commands were then removed.
Delivery preflight checks the clean packet.

Repository searches and `tools/downstream.py --uses` found no other consumer of
this namespaced tensor predicate, the endpoint functor, or the endpoint comparison
definitions. Edge cases retain all Bool endpoints, repeated fields, identity
inclusions, arbitrary ramified towers, and arbitrary arrows; the arguments use
only categorical laws and the existing universally quantified coherence fields.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
