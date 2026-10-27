## What changed

Proved three existing lemmas in `Sheaf.Paper.CanonicalTateComparisons`.
Added a proof-only import of
`Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` for its normalized
adjunction comparison. The scalar-line comparison composes the inverse completion
map with the ordinary single comparison and the scalar-line map; cancellation
proves uniqueness. The reduction counit follows its defining K-flat clause.

## Proved and sorry left

Closed three of fourteen original holes; added zero holes. All declarations are in
`WeilConjectures.CanonicalTate`, node `def-pur-canonical-tate-comparisons`.

Proved: `finiteRealization_existsUnique`, `integralScalarLine_existsUnique`,
`integralReductionCounit_isIso`.

Sorries left: `finitePullSheaf_existsUnique`, `integralProductComplex_existsUnique`,
`finiteProductComplex_existsUnique`, `integralGood`, `finiteGood`,
`integralTensorUnit_isIso`, `integralPullUnit_isIso`, `finiteScalarSheaf_existsUnique`,
`commonProduct_existsUnique`, `ordinaryReductionSquare_existsUnique`,
`ordinaryPulledLine_kflat`.

## No longer needed

No original imports, dependencies or modules are removed. The attempted flat-single
normalization and bounded-flat proof imports were removed with the three K-flatness
proofs: those versions exceeded the delivery compile limit. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No signatures or definitions changed. The node had no numbered proof plan; its
existing docstrings described the arguments. The node now records the three proofs.
The unit route is unchanged. Six holes were initially closed, but the delivery's
probed compile exceeded 60 seconds; this packet retains the independent three.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
