## What changed

Filled `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteBundleSectionAdjoint_scalar`
without changing its signature, public imports, or any shared definition. Added the proved
coefficient factorization `Sheaf.Paper.FiniteCoefficientTensorFactorization`, the proved
trace helper `Sheaf.Paper.FiniteVectorIntegrationScalar`, the proved scalar-unit
normalization `Sheaf.Paper.FiniteScalarUnitNormalization`, and proof-only imports.

The trace helper factors the normalized coefficient comparison through the common exponent
N. Root-kernel monicity identifies its root map, and the scalar adjunction plus the root-line
universal property identifies its sheaf map. Derived normalization and induction identify
its ordered tensor map. The existing common-exponent `vectorTraceScalarDescent` and
`finiteGeneralRingIntegrationExponent` then give the trace square. The parent proves the
adjunction-mate calculation and section cancellation explicitly with private categorical
lemmas. Its DAG proof now records this route.

The item had been quarantined for an older transitive import failure. The current server
queue, rework row and compiler record were read; its source was preserved and restored.
The original source compiled against the published artifacts before proof work began.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteBundleSectionAdjoint_scalar`
(node `lem-sp-finite-bundle-section-adjoint-scalar`).

Also proved the new helper
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteVectorIntegration_scalar`
(node `lem-sp-finite-vector-integration-scalar`). The public
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteCoefficientTensor_factor`
(node `lem-sp-finite-coefficient-tensor-factorization`) supplies its coefficient
factorization. The private generator and bifunctor calculations are complete.
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteScalarUnit_normalization` is also proved.

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered files: 0.
No split-off unproved statements. The proof uses the existing declared dependencies
`vectorTraceScalarDescent` and `finiteGeneralRingIntegrationExponent`; their proofs remain
work for their own items.

## No longer needed

No original public imports were removed, and no existing module was withdrawn.
`lem-pur-integration-transpose-scalar-mate` / `Sheaf.Paper.IntegrationTransposeScalarMate`
is unnecessary as a direct proof dependency here: `scalar_adjunct` proves the required
plain adjunction calculation directly, using naturality and the triangle identity. That
module has other consumers and is not claimed globally pruned.

The old direct plan to redo Kummer projective-line and affine-frame descent is unnecessary
in this item. `lem-sp-p1-kummer-derived-scalar` and `def-amb-vector-integration` are no longer
immediate proof dependencies of the parent: existing vector scalar descent and the
fixed-ring exponent theorem encapsulate those arguments. Their modules remain transitive
dependencies, so no global pruning of them is claimed. The finite coefficient arrows remain
a statement dependency. Compact scalar coherence, section compositors, and bundle adjunct
definitions are still used.

## Where the brief, the DAG or earlier work was wrong

There is no statement correction. The prior DAG treated the different-exponent trace
square as a new extension of the common-exponent argument. The library already contains
`Sheaf.SecSmoothPurity.FiniteGeneralRingIntegrationExponent`, which supplies the missing
exponent step for arbitrary finite commutative rings, not only finite fields. Combining it
with common-exponent scalar descent removes the need to split that geometric obligation
again. The unit's realized route is untouched.

The normalization checks include rank zero, N=M, the zero ring, empty schemes, and nonflat
coefficient homomorphisms: all calculations use the stated derived functors and normalized
generators, with no division or extra nonzero hypothesis.

## New nodes

`lem-sp-finite-vector-integration-scalar`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-vector-integration-scalar.json`, records the
proved trace square before exceptional transposition and zero-section pullback. It uses
the two existing geometric trace theorems, with complete Lean glue; it adds zero holes.
`lem-sp-finite-coefficient-tensor-factorization`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-coefficient-tensor-factorization.json`, records
the proved coefficient-only factorization. It is separated from the trace module after
profiling located expensive checks in canonical derived-functor conversions; the proof
uses explicit functor applications and cached instances to reduce those conversions.
The new theorem nodes are proved, with no split-off holes. There are no change records because
no existing interface or other existing module was changed.

`def-pur-vector-trace-scalar-coefficient-data` records the unchanged existing
`VectorTraceScalar.balancing`, `line`, `unit`, and `base` definitions in
`Sheaf.Paper.VectorTraceScalarDescent`. The coefficient-only theorem refers to these
constructions, not to the scalar-descent theorem in its statement. This definition node
adds no Lean file, declaration, or hole and changes no existing definition.

`lem-sp-finite-scalar-unit-normalization`, in
`dag/nodes/sec-smooth-purity/lem-sp-finite-scalar-unit-normalization.json`, records
the proved identity between transported and multiplication-normalized scalar units.
Profiling first reduced the concrete conversion by proving it for arbitrary coefficient
categories, then separated this calculation to keep every compile within 60 seconds.
It adds zero holes.

Validation: all four delivered modules compiled individually through lcompile.py.
The final parent compile took 42.7 seconds; the trace and scalar-unit modules took
47.9 and 55.2 seconds. The coefficient factorization compiled in 51.0 seconds.
No profiling options remain. The original parent theorem signature was compared
verbatim with the current shared source and is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteBundleSectionAdjointScalar": "2d77ce16fd6f5ff2752463c29343c1e65da10cb0", "Sheaf.Paper.FiniteCoefficientTensorFactorization": "969c072b72584dec0f6ee14d6371220d4ff14171", "Sheaf.Paper.FiniteScalarUnitNormalization": "75a318c2a191e7e4c18da7746465d5e04dbcf051", "Sheaf.Paper.FiniteVectorIntegrationScalar": "1bfabdc1b43ea07db76bf82f24099d392eabfad1"}, "results": {"Sheaf.Paper.FiniteSectionIntegratedScalar": {"hash": "129a629de40b93eba99d1b77e71146b7c8b2751b", "status": "OK"}}, "seconds": 101, "time": "2026-10-28T01:34:59+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
