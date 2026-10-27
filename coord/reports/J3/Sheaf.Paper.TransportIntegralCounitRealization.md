## What changed

Completed the combination proofs of `condensed_stage`, `chart_realization`, and
`integral_counit_realization` in `Sheaf.Paper.TransportIntegralCounitRealization`.
All eight existing public theorem names, complete statements and pre-existing public
imports are unchanged. To meet the per-file compilation limit, the stage, scalar,
condensed, chart, composition and base-change declarations are relocated into
proved modules and publicly re-exported by the item. Each declaration's node
attachment moves with it. The item retains the simultaneous assembly. Existing
private helpers move with the proofs that use them; no proof is replaced by a hole.
The other new imports are private proof imports. Local opacity settings keep the
large trace, realization and restricted-adjunction constructions abstract during
the simultaneous proof. These local attributes change no published interface.

The condensed proof composes the two encoding equivalence adjunctions with the
integral adjunction and transports along the operation comparisons. The existing
`exists_equivalenceAdjunctionComparison` gives the unit and counit comparisons;
right-adjoint uniqueness supplies the fixed-counit formula.

The chart proof constructs the actual gamma natural isomorphism by the inverse
coordinate realization and its inverse unit. It transfers the original charts
through gamma. The private proved lemma `chart_counit_transport` carries out the
naturality and inverse cancellation in the chart counit word.

The new proved `normalized_integral_trace_data` specializes
`tower_trace_purity_comparison` to the actual base orientation and retains its
integral orientation, scalar-trace and trace-transpose equations for one model
system. The item chooses the integral and condensed stages for that same system
and assembles those equations. Separating this projection also keeps the two large
comparison specializations outside the fieldwise assembly's heartbeat budget. The factorization through
`gammaH` follows from `gammaH_eq`; every factor is an isomorphism. Three new modules
isolate the remaining geometric comparison steps, described below. The item node's
proof, proof dependencies and proof origin now follow this assembly.

Validation: the split modules and simultaneous assembly passed the server's
60-second per-file check. Profiling settings were then removed. All eight original
statement texts and every new node attachment were checked against the Lean files.
There are no current direct Lean importers of the item.

## Proved and sorry left

The three original holes now have complete Lean combination proofs:

- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.condensed_stage`;
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.chart_realization`;
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.integral_counit_realization`.

Three holes are added, each in its own new module, with its source and complete
proof in words:

- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.condensed_integral_endpoints`
  (`lem-pur-condensed-integral-endpoints`);
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.specified_tower_adjunction_charts`
  (`lem-pur-specified-tower-adjunction-charts`);
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.fixed_presentation_uniformizer_reductions`
  (`lem-pur-fixed-presentation-uniformizer-reductions`).

There are zero remaining holes in the item module, zero in the six new proved
modules, and three in the packet.
This is a decomposition of three holes into three strictly smaller geometric
steps, not a net hole reduction or an axiom-free proof of the targets. The first
step has no adjunction or counit conclusion; the second has no gamma or transported
adjunction; the third concerns one fixed coefficient presentation and assumes the
unit normalization and trace-transpose equality supplied separately by the existing
comparison theorem.

## No longer needed

No pre-existing public import, Lean module or declaration is removed, and no global
module pruning is claimed. All moved declarations are publicly re-exported. No pre-existing proof import was removed.

The item's direct proof dependencies no longer include:

- `lem-weil-pbc-finite-type-over-noetherian`: Noetherian instances are already binders
  or fields of the supplied realization;
- `sk-thm-existence`: the fixed-counit calculation takes the specified adjunction
  as input and uses right-adjoint uniqueness;
- `prop-pur-adic-reconstruction-trace-coherence`: trace equality comes from the
  existing trace comparison; the already-proved geometric clauses directly map
  the whole-tower factor equations;
- `lem-sp-tower-coordinate-adjunction`, `lem-pur-diagonal-dnc-chart-normalization`,
  `lem-sp-orientation-scalar-tower-transport`, and `det-sp-tower-p1-adjunction`:
  the formal chart transfer uses the supplied gamma and original chart counit,
  rather than identifying gamma by a second orientation calculation.

The obsolete top-level tool approvals for the Noetherian construction,
diagonal-DNC comparison, and orientation-scalar comparison were removed from the
item node. The other tool approvals remain in order. These nodes may remain
needed elsewhere or underneath the cited chart and gamma theorems.

The former direct dependencies `sk-lem-integral-models`,
`det-sp-normalized-equivalence`, `det-sp-integral-direct-image-tower`,
`lem-sp-strict-tower-arithmetic-restriction`, `det-sp-tower-gluing`,
`lem-pur-tower-purity-realized-transpose`, and
`lem-pur-tower-trace-purity-comparison` now belong to the respective new smaller
steps. They have not been pruned from the argument. The base-change factor theorem likewise
remains used by the extracted proved realization module.

## Where the brief, the DAG or earlier work was wrong

No target or existing statement was changed or disputed. The planned chart
orientation identification is unnecessary for the formal statement as written:
`m.realization.purity` already provides the natural invertible gamma, and the
transported adjunction's counit is defined using that same gamma.

The uniformizer reduction step must retain normalization hypotheses. An arbitrary
source realization comparison is not normalized merely because it is invertible.
The new fixed-presentation statement therefore explicitly assumes the prescribed
unit reductions and equality with the trace transpose. The simultaneous comparison
theorem supplies both hypotheses in the original model system.

The unit's integral realization, trace, coefficient and chart route is preserved.
No source-library declaration was modified and no shared interface was changed.

## New nodes

`lem-pur-condensed-integral-endpoints` in
`Sheaf.Paper.CondensedIntegralEndpoints` states only the normalized integral/condensed
encodings, membership in the precise full subcategories and the two operation
comparison isomorphisms. It is the geometric input to an explicitly proved
adjunction transport.

`lem-pur-specified-tower-adjunction-charts` in
`Sheaf.Paper.SpecifiedTowerAdjunctionCharts` transfers the existing gluing charts to
the supplied original tower adjunction at its fixed compactification. The item
constructs gamma and proves the further transported chart-counit equation itself.

`lem-pur-fixed-presentation-uniformizer-reductions` in
`Sheaf.Paper.FixedPresentationUniformizerReductions` is the uniformizer-reduction
part of the simultaneous conclusion for one normalized coefficient presentation,
assuming the independently supplied orientation normalization and trace-transpose
equality. The item proves the simultaneous model, stage, trace, and factorization
clauses from existing declarations.

There are no change records: only the item, its node, and the new modules and their
nodes are changed.

`lem-pur-integral-base-change-realization` in
`Sheaf.Paper.TransportIntegralBaseChangeRealization` contains the already-proved
Cartesian base-change realization clause, with no sorry. It maps the two given
whole-tower factor equalities through the inverse coordinate equivalence and total
limit while retaining the two finite comparison certificates. Its extraction is
solely to separate the expensive kernel/linter check and serialization. The item
publicly re-exports the original declaration with its original name and signature.

`lem-pur-normalized-integral-trace-data` in
`Sheaf.Paper.NormalizedIntegralTraceData` is proved by specializing the existing
comparison to its own invertible base orientation and projecting its integral
scalar/trace equations. It adds no hole. Its conclusion omits the integral and
condensed stages, gamma factorization, charts and uniformizer comparisons, all of
which are handled separately in the item.

`lem-pur-integral-stage-construction` in
`Sheaf.Paper.TransportIntegralStageConstruction` carries the already-proved
`integral_stage`, `coefficient_stage` and `fixed_coefficient_stage` declarations,
including their proved private transport helpers. All signatures and proofs are
retained. No new mathematical assertion or hole is introduced.

`lem-pur-condensed-stage-realization` in
`Sheaf.Paper.TransportCondensedStageRealization` carries the completed
`condensed_stage` combination proof from the encoding endpoint lemma and the
existing equivalence-adjunction comparison theorem.

`lem-pur-integral-chart-realization` in
`Sheaf.Paper.TransportIntegralChartRealization` carries the completed
`chart_realization` proof: it constructs the actual gamma and transfers the given
original-adjunction charts by the proved naturality/cancellation identity.

`lem-pur-integral-composition-realization` in
`Sheaf.Paper.TransportIntegralCompositionRealization` carries the existing proved
`Coherence.composition_realization` declaration and its functorial equality helper.
Its signature and proof are unchanged.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
