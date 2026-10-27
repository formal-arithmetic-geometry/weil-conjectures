## What changed

Closed `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso` in
`Sheaf.Paper.PuritySourceTransports`. Added private proof imports of
`Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete` and
`Sheaf.Paper.QcqsCompletionUnitCriterion`. The existing proof import of
`Sheaf.Paper.StrictTensorAugmentationNormalization` becomes `import all` so the
proof can use its already-proved `map_normalized` helper directly.

The existing calculus tensor comparison identifies the ordinary total with the
ordinary derived tensor. Apply `finiteTorOrdinaryTensorComplete` and
`canonicalCompletionUnitCriterion`, and transfer invertibility of the completion
unit through that representative isomorphism. The total is good by `tensor_good`;
the defining completion-unit equation therefore proves invertibility of the
localized strict Roos augmentation. The normalized coordinates identify the item's
chosen tensor augmentation with `StrictTensorAugmentation.map`, using the
existing `map_normalized` lemma for the coordinate verification.
The normalization and chosen-witness identity are proved in private helpers with
local reducibility settings. A third generic private helper maps the composite
with a tower isomorphism, avoiding instance search across coefficient-category
presentations. The component is the strict Roos augmentation followed by the
Roos image of the tensor-tower isomorphism, so its image in the derived category
is invertible.

The item module, its own DAG node, and a change record are changed. The
`ordinaryTotal` body now reuses `coefficientTotalTensor` directly instead of
expanding that same signed direct-sum tensor. This avoids expensive repeated
kernel conversions while preserving its type and mathematical meaning. Existing
declaration signatures, public attributes and public imports are preserved.
The ten direct importers and the explicit indirect `ordinaryTotal` user
`Sheaf.SecSmoothPurity.RationalPurityLineComparisons` all compile against the
changed definition within the per-file limit. The final direct importer
`RationalPurityExchangeEndpoints` passes in 44.3 seconds. All unchanged consumer
test copies and temporary profiling options have been removed. No consumer adaptation is needed. The change record is
`coord/changes/G1-purity-source-canonical-ordinary-total.md`. The DAG now records
the completion and strict-map arguments instead of describing this theorem as an open obligation.

The completeness and unit-criterion nodes are used as tools from the six-functor
unit. They give the precise ordinary-operation completeness and fixed-unit
criterion required by the existing docstring argument. The item's unit has no
realized statement or steps to bypass. No new tool approval is written here.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso`
(node `def-pur-canonical-purity-source-transports`).

No `sorry` remains in the item module. No holes or split-off statements are added.
This is a proof from existing library declarations, including any outstanding
obligations below those declarations, not a claim that their entire dependency
closure is axiom-free.

## No longer needed

None. No imports, nodes, modules or declarations are withdrawn. The existing
localization and normalization proof dependencies remain needed. The new proof
uses the stated general finite-Tor completeness theorem directly; the stronger
qcqs and residue-characteristic assumptions of `constructibleTensorCompletion`
are unnecessary and that theorem is not used for this proof.

## Where the brief, the DAG or earlier work was wrong

No statement repair is needed. During consumer validation the live library
received E9's subdivision of `RationalPurityTraceCoherence`; the explicit
`ordinaryTotal` user is now `RationalPurityLineComparisons`. Its unchanged source
passes against this delivery in 27.3 seconds. The obsolete pre-subdivision test
copy is removed rather than adapted or delivered.

Profiling exposed the cost of comparing the
manually expanded `ordinaryTotal` presentation with the existing canonical
`coefficientTotalTensor`; the definition now uses that presentation directly. The earlier DAG accurately left
`tensorAugmentation_isIso` open but did not cite the now-existing general theorem
`finiteTorOrdinaryTensorComplete` or the general completion-unit criterion. Those
results supply its docstring's completeness step without adding any assumptions
on the scheme. The original strict normalization, including the zero shifted
coordinate, is retained throughout; no comparison map is chosen from its quotient
projections alone.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
