## What changed

`Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar` now contains a complete Lean
proof of `AlgebraicGeometry.Etale.finite_smooth_dualizing_scalar`, with its public
signature unchanged. It privately imports `OrdinaryChartExceptionalScalar` and the
existing `EtaleDerivedJointlySurjectiveConservative` theorem.

The proof specializes the local chart mate square to the coefficient unit, moves
the scalar unit isomorphism through the B chart comparison by naturality, and
identifies the resulting arrow with the published dualizing map. A proved private
helper constructs smooth charts over the original Noetherian base from the
upstream pure-relative-dimension normal form. Isomorphism cancellation on each
chart, followed by jointly surjective derived pullback detection, gives the global
claim. The empty source is covered by the same point-indexed family argument.

Added one local chart compatibility theorem in
`Sheaf.SecSmoothPurity.OrdinaryChartExceptionalScalar`, with its source, full proof
in words and matching DAG node. It concerns the actual mate on a single chart,
not an alternative definition of the dualizing object.

The item and the new supporting module compile individually through lcompile.py;
the import-ordered compile of the pair is checked again by deliver3.py, including
its axiom probes. The clean item compile after import pruning took 16.0 seconds.
No source-library files, shared definitions, target signatures or instances change.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.finite_smooth_dualizing_scalar`
(node `lem-pur-finite-smooth-dualizing-scalar`). The item's actual hole count is zero.
Its coordinate-cover helper is also completely proved.

Added one supporting hole:
`AlgebraicGeometry.Etale.ordinary_chart_exceptional_scalar`
(node `lem-pur-ordinary-chart-exceptional-scalar`), whose proof is exactly `by sorry`.
This is the only hole left in the two delivered modules. No definition has a hole.

This is a decomposition: one upper hole closed, one local hole added, net zero
holes closed. The global isomorphism argument and the transport through unitIso
are proved, so the new statement is strictly a local step of the original argument.
It neither asserts global invertibility nor packages the two original conclusions.
Its arbitrary-input version permits the direct adjunction-counit calculation,
without a global smoothness, cover or free-unit normalization conclusion.

## No longer needed

No baseline direct import is removed: `DncCoefficientTransportData` is needed by
the unchanged public signature, including the published dualizingMap.
Two redundant imports tried during development, `OrdinaryFiniteP1Adjunction` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`, were omitted because
those declarations are already publicly available through the original import.
The source `SmoothDuality.Local` import used during development is replaced by the
existing smaller Sheaf conservativity module matching its DAG node.

The old direct proof route through `det-sp-reduction-exceptional` and
`det-sp-scalar-extension-functor` is not used: its intrinsic right adjoints require
a positive-characteristic field presentation absent here. The new proof uses the
ordinary normalized chart maps, not the intrinsic realization or constructible
subcategory existential witnesses. The old direct proof dependency
`lem-asd-etale-finite-twist-pullback` is needed only in the remaining local chart
argument and the normalized P1 data, so is recorded there rather than as a direct
step of the item. The reduction-exceptional node remains a statement dependency
for the published chart constructions. All transitive dependencies through the
original public import remain; no node or module is claimed globally unreachable,
and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof paragraph says to specialize `reductionExceptional_isIso`.
Its current Lean statement requires schemes of finite type over a field k with
positive characteristic different from ell, and coefficient rings in its intrinsic
presentation. The item instead quantifies over arbitrary Noetherian schemes and
ordinary coefficient rings. For example S=Spec Z[1/ell], g=id, d=0 satisfies the
item's scheme conditions but admits no such positive-characteristic field base.
The chart and raw-counit lemmas inspected in `ReductionExceptionalChart`,
`ChartCounitScalarTransport`, `RawChartScalarCounitPasting`, `AffineCounitScalar`,
`AffineLineCanonicalScalarCounit` and `P1CounitScalar` retain these field-base
hypotheses too. The new local theorem records the remaining ordinary-site
calculation without silently adding a field hypothesis.

Checked the live server queue, rework, return and claim records before working.
The live queue marks this as a one-hole proof item, not a zero-hole repair.
The snapshot build-error file records an older bad dependency import. The current
published environment compiles the unchanged original module in 6.5 seconds;
the present delivery also compiles with its new proof.

The new local equation was checked mathematically on dimension zero (only the
etale sum adjunction), identity coefficients, the empty chart, zero rings, and the
nonflat quotient Z/ell^2 to F_ell. Its Tate line is locally free of rank one over
A, so no B-over-A flatness is used. The unit's diagonal/deformation route above
this coefficient-theory substep is unchanged; its realized node lists are empty
in this snapshot and no unit or chapter record is edited.

## New nodes

`lem-pur-ordinary-chart-exceptional-scalar`, module
`Sheaf.SecSmoothPurity.OrdinaryChartExceptionalScalar`: scalar naturality of the
counit-normalized ordinary exceptional right-adjoint comparison on one etale
affine chart. It isolates the Charts paragraph of the same source. Searches with
LeanFinder, LeanSearch, Loogle and Mathlib grep are in searches.jsonl and the node;
the blueprint search found the field-base reduction-exceptional package, not a
version with these Noetherian hypotheses. The item node's proof, proof_deps and
proof_origin now describe the actual Lean assembly.

Change record: `coord/changes/M1-ordinary-chart-exceptional-scalar.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar": "7b2817a7f9a13b413b48c8fcca1cc44ed967fe25", "Sheaf.SecSmoothPurity.OrdinaryChartExceptionalScalar": "958b7ce8e62f7ae84f614fa5e5ec06ebb677e4c3"}, "results": {"Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation": {"hash": "d0e996de75c401dd5753905d7cd699ae18a9754b", "status": "OK"}, "Sheaf.SecSmoothPurity.PurityDncCoefficientTransport": {"hash": "c64cdfd0e3353b1347b0d248a769b50b6acb9ed7", "status": "OK"}}, "seconds": 309, "time": "2026-10-28T03:27:18+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
