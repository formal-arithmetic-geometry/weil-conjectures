## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_internal_right`
with the existing signed-total scalar square and localized-total path. The
canonical `mapBifunctorComparison` satisfies the total square's summand hypothesis
by its proved inclusion formula. The remaining calculation identifies the input
and output path wrappers, removes the identity functor comparison, and rewrites
the total functor's map of a pair as the native tensor map. The latter equation
is a proved private helper. A second proved private helper pastes the input
associativity equation without rewriting the entire concrete diagram. Two proof imports supply the existing square and path;
public imports, definitions, and the theorem statement are preserved.

The item's DAG now records these applications explicitly. Local reducibility
attributes retain the large derived and total constructions while doing the
wrapper calculation; cached instances are the existing instances.

Profiling found that simplifying whole comparison-isomorphism records and
rewriting the complete input diagram produced expensive kernel conversions.
Definition reduction on the wrapper projections, followed by the generic input
pasting lemma and direct equality composition, reduced the measured compile from
66.9 seconds to 56.4 seconds. Profiling options are removed for delivery.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_internal_right`
(node `lem-sfb-quotient-section-tensor-transport-internal-right`). No holes are
added, none remain in the delivery, and no statement is split off. The private
helpers `internal_right_total_tensor_map` and `paste_input_path` are proved.

## No longer needed

No import is removed and no module is withdrawn or pruned. The old direct proof
references to `lem-pe-internal-section-tensor-comparison`,
`lem-weil-pbc-independent-sheaf-tensor-colimits`, and
`lem-pd-section-derived-tensor-normalization` are replaced by the two existing
proved square/path nodes, which package the same ordinary and localization work.
These earlier dependencies remain needed transitively; this delivery does not
claim to prune them. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The obligation does not require another decomposition: the existing
`section_tensor_total_scalar_square` and `section_tensor_total_localization_path`
already contain the ordinary-generator, signed-total, and localization arguments
in its plan. Supplying the canonical summand formula and identifying the wrappers
closes it. No disputed statement or definition repair was needed. The current
snapshot lists a one-hole proof item, with no rework row or build-error file.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportInternalRight": "c4ca63d08411cdbe1e51d38f2e0a9bc628e1dd41"}, "results": {"Sheaf.Paper.QuotientSectionTensorTransportInternalCounit": {"hash": "b46dbc485f7ddea063001f3c35ccf110e0e0f5dc", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T06:33:06+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
