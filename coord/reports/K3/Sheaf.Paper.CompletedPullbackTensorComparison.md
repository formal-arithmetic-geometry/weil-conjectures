## What changed

Prove `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique` by uniqueness of
composite left adjoints. The two right adjoints agree through the actual quotient-ring
naturality square. Reuse the proved private ring square, direct-image/scalar-restriction
comparison, and composite-unit calculation in `StrictScalarPullbackComparison` through a
proof-only `import all`. The existence witness is the canonical `leftAdjointUniq`.
For uniqueness, apply the composite adjunction Hom equivalence, evaluate on sections,
and use the two normalized scalar-extension units. Update the owning DAG proof to
record these exact dependencies. Existing declaration signatures and definitions stay
identical.

Validation: the complete item compiled through `lcompile.py` in 36.1 seconds,
exit code 0, with no diagnostics. A subsequent instrumented delivery compile exceeded
60 seconds. Profiling found costs spread across elaboration and type checking. Local
irreducibility annotations keep the chosen ordinary and complex comparisons behind their
named APIs during subsequent elaboration. These local attributes do not change the
exported interface. The final delivery compile checks the optimized file again.

The argument applies to arbitrary module sheaves, empty schemes, zero modules, the
first positive quotient, and the identity quotient `n = m`. It assumes neither flat
input modules nor flat quotient maps. It uses the actual intrinsic adjunction units,
not a replacement normalization.

## Proved and sorry left

Closed one of the original nine holes:
`WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`.
No holes added or split off. The proof uses the existing normalized quotient calculus;
its dependencies may still contain their own previously recorded holes.

The eight unchanged holes left in this module, all attached to
`def-pur-completed-pullback-tensor-comparison`, are:

- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

None. No module or node is withdrawn, and no existing import is removed. The ordinary
quotient comparison needs no new intermediate statements: the strict scalar-pullback
module already proves the requisite general composite-adjunction calculation.

## Where the brief, the DAG or earlier work was wrong

The ordinary quotient normalization was still recorded as an open obligation despite
the existing proved strict scalar-pullback helpers supplying its construction and
unit equation. This delivery specializes those helpers to the intrinsic finite
pullback adjunction and proves the remaining uniqueness assertion. No disputed
statement, definition repair, change of target, or change of the unit route is involved.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
