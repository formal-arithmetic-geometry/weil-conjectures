## What changed

The assigned `component_extension` theorem now obtains the finite Hom scalar
compatibility from `RationalOperations.rationalHom_scalar_evaluation` and applies
the categorical scalar-pasting lemma. The pasting obligation is isolated in the
new module `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting`.
Both modules compile together in import order.

## Proved and sorry left

Closed `WeilConjectures.CoefQbarVerdier.HomComparison.component_extension`.
One strictly smaller intermediate theorem remains sorry:
`WeilConjectures.CoefQbarVerdier.HomComparison.component_extension_of_scalar_compatibility`.
It assumes the finite Hom scalar evaluation square and states the resulting
common-stage component square.

## No longer needed

The assigned theorem's proof does not directly use the former broad dependency
list `lem-coef-integral-finite-extension`, `lem-sf-rational-hom-identifications`,
or `lem-zl-specified-hom-scalar-evaluation`; their roles are represented by the
existing `lem-sf-rational-hom-scalar-evaluation` theorem and the new pasting node.
No imported module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combined the finite Hom scalar evaluation calculation
with the subsequent common-stage categorical pasting. The finite scalar square is
already exposed by `rationalHom_scalar_evaluation`; the unresolved part is the
separate pasting lemma recorded in the new node. No target statement was changed.

## New nodes

`lem-coef-qbar-verdier-hom-comparison-scalar-pasting` records the strict
intermediate statement `component_extension_of_scalar_compatibility` and its
source, proof plan, searches, and Lean attachment. It is the scalar-pasting step
with the finite Hom compatibility supplied as an explicit hypothesis.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension": "07fc8904e746be96946dc114a18ebeada077a569", "Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting": "fd2ebfd1d0765340247fe85a67ef7eaaaac008ce"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison": {"hash": "23d04afbb597a934ec82ae792debddd7252c0743", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T04:34:08+0800", "transitive": 0, "version": 1}
```

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
