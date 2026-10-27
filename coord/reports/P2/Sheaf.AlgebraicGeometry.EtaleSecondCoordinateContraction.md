## What changed

Replaced the hole in `AlgebraicGeometry.Etale.CoordinateTrace.secondCoordinateContraction`
by a categorical composition of single-factor trace base change and tensor extraction.
Its statement and public imports are unchanged. Two new modules isolate the two
independent calculations. The tensor-extraction identity is proved by transposing
projection maps under the pullback/direct-image adjunction, using braidedness and
monoidal coherence. The base-change identity specializes the already proved
`etaleTensorEvaluation_constant_baseChange`, with the actual ordered projection
maps, pullback unit comparison and common-coordinate comparisons.

All auxiliary lemmas are private and proved. No shared definition, source-library
interface, instance, attribute, or target statement changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.CoordinateTrace.secondCoordinateContraction`
(node `lem-sfb-etale-second-coordinate-contraction`).

The two new public lemmas are proved:

- `AlgebraicGeometry.Etale.CoordinateTrace.projectionTraceTensorInterchange`
  (node `lem-sfb-etale-projection-trace-tensor-interchange`).
- `AlgebraicGeometry.Etale.CoordinateTrace.traceBaseChangeEvaluation`
  (node `lem-sfb-etale-trace-base-change-evaluation`).

Counts: one original hole closed, zero holes added, zero holes left in the three
delivered modules. No hole is added inside a definition. The proof uses existing
library declarations; it does not discharge unrelated existing library holes.

Validation: all three delivered modules compile in import order via lcompile.py.
The tensor calculation took 22.8 seconds and the final contraction 12.7 seconds;
the evaluation calculation previously compiled in 14.9 seconds. No compiler
warnings remain. The original theorem signature and each node's attached Lean
statement were compared with the source and agree verbatim.

## No longer needed

No original import was removed: the original module imported only its data module.
The following former planned proof dependencies are not used by this proof:

- `lem-weil-pbc-ringed-exchange-tensor-coherence`, module
  `Sheaf.Paper.RingedExchangeTensorCoherence`: ordinary etale projection/exchange
  compatibility already exists upstream and is the input of the single-factor lemma.
- `lem-sfb-ringed-projection-tensor-composition`, module
  `Sheaf.Paper.RingedProjectionTensorComposition`: the tensor rearrangement is
  proved directly from the actual etale adjunction and braided pullback.
- `lem-sfb-ringed-derived-monoidal-comparisons`, module
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`: all comparisons in this
  proof are the canonical ordinary etale comparisons already used by the data.

These dependencies are removed from this node's proof route only. No declaration
or module of the adopted source library is removed. The unit's statement and its
realized proof steps are preserved. No entire module is asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned detour through ringed-presentation comparisons is unnecessary for the
ordinary etale data in this statement. The source library already proves the
ordinary etale projection/base-change square and braided pullback comparisons.
No mathematical statement was found false or changed.

The two new statements were checked on the zero ring, zero coefficient, empty
scheme and identity morphism cases. The base-change statement does not require
self symmetry: it contracts only one kernel factor. The tensor statement does
require identity self symmetry, transported to the pullback; this is precisely
the condition needed to interchange the two pulled-back coefficient factors.

## New nodes

`lem-sfb-etale-trace-base-change-evaluation` records single-factor evaluation
base change, proved by specializing the existing canonical evaluation base-change
theorem and normalizing the unit and tensor comparisons. It removes the
independent tensor-interchange part of the original obligation, and is strictly simpler than the item. Its module is
`Sheaf.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation`.

`lem-sfb-etale-projection-trace-tensor-interchange` records the proved independent
projection calculation for one arbitrary proper morphism, arbitrary objects K,L,
and arbitrary trace. It has no self-product square, exchange morphism, coordinate
comparison or trace base-change hypothesis. Its module is
`Sheaf.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange": "92d5e80c5145d1aa0de7d282760b80b53af371dd", "Sheaf.AlgebraicGeometry.EtaleSecondCoordinateContraction": "f5a2e7f7163e86491ca9dd58d4761179f82d2b38", "Sheaf.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation": "9cf80d8ccccbc7a207647a2942db11c21cd59474"}, "results": {"Sheaf.AlgebraicGeometry.EtaleCoordinateTraceContractions": {"hash": "cf7f85bd34a609db3370ba4533695b8d17f4a454", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T00:31:28+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
