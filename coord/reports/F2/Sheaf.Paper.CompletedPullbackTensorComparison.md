## What changed

Proved `WeilConjectures.canonicalRationalPullbackTensor_scalar` by applying target
rationalization to `canonicalIntegralPullbackTensor_scalar` on the underlying
integral pair. The proof uses the published object equations and pure-tensor map
formulas for rational pullback, tensor and scalar extension. The chosen comparison
normalizations identify each of the six arrows with its localized integral arrow.
Heterogeneous equality transports the endpoints; functoriality preserves the
integral composition equality. Four proved private helpers handle transport of
maps, dependent applications, product morphisms and the definition of the
localization functor on integral morphisms.

No existing statement, definition or public attribute is changed.
Unfolding controls are local to the proof section. Explicit definitional
equalities reconcile the published tensor-coordinate and categorical Hom formulas
without disabling transparency checks. The updated node records this proof. The ordinary quotient comparison proved by K3 during
the initial source refresh is preserved and is not counted as work of this delivery.

Validation: the complete delivered module compiles through `lcompile.py` in
57.2 seconds, with no profiling options. The isolated proof also compiled.

## Proved and sorry left

Closed 1 of 8 holes in the refreshed item:
`WeilConjectures.canonicalRationalPullbackTensor_scalar`.
Added 0 holes; split off 0 statements.

The seven remaining holes have unchanged statements and source/proof docstrings,
all under node `def-pur-completed-pullback-tensor-comparison`:

- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`

The closed rational square depends on the existing integral scalar-square hole.
This is a proof from the previously stated dependency, with no new decomposition.

## No longer needed

No imports are added or removed; no node, module or unit step is withdrawn.
The rational compatibility uses the existing normalization declarations in
`Sheaf.Paper.DerivedPullbackTensorHom` and
`Sheaf.Paper.SfRationalizationKaroubi`, together with the integral compatibility
already stated in the item. No further scalar-coherence lemma is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The item initially displayed nine
holes, but the shared source refreshed with K3's ordinary quotient-comparison
proof before the sandbox copy was made. The delivery uses that refreshed source
and reports eight baseline holes. The unit record has no realized statement or
proof steps; no unit route is bypassed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
