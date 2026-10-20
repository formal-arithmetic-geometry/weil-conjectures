## What changed

Filled `AlgebraicGeometry.WeilSheaf.sum_trace_compactlySupportedCohomology` in
`WeilConjectures.WeilSheaf.GrothendieckLefschetz`. All existing declaration signatures,
attributes, definitions, docstrings and public imports are unchanged. Added private proof
imports of `WeilConjectures.PointCount`,
`WeilConjectures.WeilSheaf.LowerShriekOperations`,
`WeilConjectures.WeilSheaf.StalkCharpoly` and
`WeilConjectures.WeilSheaf.TraceFunctionCongr`.

Apply the existing
`WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction` to
`WeilSheaf.toComplex.obj F`. Compactly supported cohomology agrees by definition, and
`WeilComplex.traceFunction_toComplex` identifies its trace function with that of `F`.
Then apply `Scheme.Hom.finsum_fieldPoints_eq_sum`, using
`WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow` for each fiber. Take the finite
set of closed points of degree at most `m`; every degree dividing the positive integer
`m` lies in it. The summand outside this finite set is zero, so
`finsum_eq_sum_of_support_subset` identifies the resulting finite weighted sum with the
required finsum. Finally convert natural-number scalar multiplication into multiplication.

This specializes the already stated complex trace formula, which carries the same blueprint
reference `thm-trf-grothendieck-lefschetz-qbar`, and implements the closed-point regrouping
of unit `sk-thm-trace-transport`, Step 5. It does not replace the unit's trace-formula route.
No new statements or nodes are needed. In particular, the existing complex trace formula's
proof obligation is retained; it is not proved by this packet.

Validation: compiled the item through `lcompile.py`, exit code 0, no warnings, 3.3 seconds.
The proof uses `m ≠ 0` exactly to bound degrees dividing `m`. Empty schemes and the zero
sheaf cause no special assumptions: the point-counting and finsum support lemmas apply
to empty supports as well.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.WeilSheaf.sum_trace_compactlySupportedCohomology`
(blueprint `thm-trf-grothendieck-lefschetz-qbar`, degree-zero specialization and the
closed-point form of `sk-thm-trace-transport`, Step 5).

There are zero remaining sorries in the item and zero holes added anywhere. This is a
proof from existing stated dependencies, not a decomposition into new holed lemmas.
The imported
`AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`
retains its pre-existing sorry; it is an input with the same blueprint reference, not a
hole introduced by this delivery. The trace formula node is listed among the batch-5
assumptions in `coord/assumed.tsv`.

## No longer needed

No imports, declarations, nodes or modules are removed or withdrawn. The finite-stage
trace transport and Karoubi comparison are not reimplemented in this specialization:
they remain the responsibility of the existing complex trace-formula declaration.
Nothing in their route is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The shortest available route is the already
stated source-library trace formula for Weil complexes, followed by the existing proved
weighted point-counting theorem. No categorical-to-ordinary trace bridge or new
finite-stage transport lemma is required in this module.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
