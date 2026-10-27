## What changed

Prove `WeilConjectures.PurCompactSupport.projectionDomain_complete` in
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`, with its statement unchanged.
The private helper `projectionTensorConstructible` transports through the existing
`integralDetailedTransport`, applies the already proved private
`transported_tensor_constructible` from `WfConstructibleTensorKoszulUnit`, and transports
back along `ProjectionTensorCoefficient.ordinaryComparison`. The characterization
`integralStratifiedPerfectDetailed` identifies the two constructibility predicates;
`pbcIntegralUniformComplete_isTriangulated` supplies invariance under isomorphism.

The private helper `projectionPullConstructible` identifies the completed coefficient
maps by their finite projections, compares the module pullbacks by adjoint uniqueness,
and compares their derived functors by the left-derived universal property. It then
applies `ordinaryCompletedIntegralPullback`. The main proof supplies noetherianity,
finite dimension and prime invertibility from the given finite-field hypotheses,
uses the existing compact-support constructibility assertion, and applies the tensor
helper to the two required pairs. Both private helpers are proved with no postponed
steps. No public signature, definition, target or public import changes.

Add proof-only imports of `WfConstructibleTensorKoszulUnit` (using `import all` for its
proved private helper), `ProjectionTensorCoefficientComparison`,
`IntegralStratifiedPerfectCharacterization`, `PbcUniformCompleteTriangulated`,
`OrdinaryCompletedIntegralPullback`, `SfIntegralConstructibleTriangulated`, and
`WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField`. The first six are under
`Sheaf.Paper`. Update the owning node's proof, proof dependencies and proof origin.

For checking cost, the existing private `tensorPair_map` and `tensorPair_ext` proofs
use a new proved private equation `tensorPair_eq_pure` between the existing pure-section
notations. The existing private `scalarRightKanShift_unique` now uses the already proved
private `Functor.kanShiftHom_ext` via a proof-only `import all` of the existing source
module. Local reducibility attributes keep the large scalar-extension and total-tensor
constructions abstract during proof elaboration. Local priorities select the existing
`HasSheafify.isRightAdjoint`, `HasColimitsOfShape.has_colimit`, and the existing module-sheaf
colimit instances directly, avoiding repeated generic searches. These are proof-context
changes, not public definition changes. The complete module compiled in 49 seconds with
profiling enabled; the delivered source removes those diagnostic options.

## Proved and sorry left

Closed one of the sixteen current holes:
`WeilConjectures.PurCompactSupport.projectionDomain_complete`.
Added zero holes and split off zero statements. The proof uses existing library
statements, including the existing `integralCoefficientComparison` and normalized
ordinary tensor comparison; it does not claim that their import closure is axiom-free.

Fifteen original holes remain, all in node
`lem-pur-compact-support-integral-coefficient-comparison`, in namespace
`WeilConjectures.PurCompactSupport`:

- `comparison_commShift`
- `comparison_composition`
- `comparison_identity`
- `scalarOrdinaryTensor_existsUnique`
- `scalarTensor_existsUnique`
- `openComparison_isIso`
- `finiteComparison_isIso`
- `integralCoefficientComparison`
- `recordedIdentification_existsUnique`
- `reductionComparison_isIso`
- `refinementProperOpen_existsUnique`
- `comparison_refinement`
- `refinementComparison_coherence`
- `comparison_strict_towers`
- `comparison_projection`

## No longer needed

None globally. No original imports, nodes or modules are withdrawn. The seven planned
compact-support coefficient helpers remain relevant to the unresolved assertions.
The completed projection-domain argument does not use the planned declarations in
`CompactSupportCoefficientModels`, `CompactSupportStrictScalarMate`,
`CompactSupportScalarLimitReduction`, `CompactSupportStrictScalarRefinement`,
`CompactSupportScalarProjectionIdentification`, `CompactSupportStrictScalarComposition`,
or `CompactSupportScalarShiftNormalization`: it only needs constructibility of the two
tensor arguments. These are unused in this subproof, not globally pruned dependencies.

## Where the brief, the DAG or earlier work was wrong

The seven planned upper helper modules depend back on this module through
`CompactSupportCoefficientModels` and cannot simply be imported here. This delivery
completes the separate projection-domain assertion using independent existing APIs.
The original unit route and all statements are preserved. There are no definition
repairs, forced adaptations or new nodes.

During this session the shared source withdrew `ScalarOrdinaryTensorExistence` and
restored `scalarOrdinaryTensor_existsUnique` as a hole. The packet uses that current
source and does not restore the withdrawn import or public uniqueness helper. Counts
use the sixteen current holes, not the earlier fifteen-hole snapshot.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
