## What changed

Continue the existing smooth-purity reconstruction argument without changing any
existing public signature, public import, exported attribute, instance, or data
construction in `WeilConjectures.SmoothPurity.Defs`.

Proved the private `smoothTrace_normalizedIntegralSystem`: instantiate the existing
reconstruction theorem on the native finite levels and quotient comparisons,
retaining strict Tate/unit towers, projection normalizations, both reconstruction
assertions, and inverse exceptional quotient squares. Proved the private
`smoothTrace_reconstructedInverseSemilinearSquare` by transposing the actual
inverse coefficient-linear square under scalar extension/restriction adjunction.

Added the completely proved module `Sheaf.SmoothPurity.TraceNonuniqueness` and its
public theorem `not_existsUnique_representing_trace_at_point`. The canonical open
comparison gives a representing trace for the identity of a separably closed
point. Precomposition with the sign automorphism gives a distinct representing
trace. Evaluation at a singleton proves the sign is nontrivial in the actual
condensed coefficient module; faithful point pullback, the single functor, and
unit comparisons transport this to the bounded constructible unit. The proof
uses neither `existsUnique_smoothTrace`, `smoothTrace`, nor the disputed purity
instance. The item privately imports and applies this diagnostic theorem before
its disputed instance. No contradiction is used to close an original hole.

Seven proved generic private helpers factor existing unit/naturality, inverse
reduction, semilinear, composite-adjunction, and inverse-comparison calculations.
Local irreducibility prevents unnecessary unfolding. Profiling a further
61.8-second check showed repeated categorical elaboration and typeclass work; the
item now also keeps the module monoidal structures, internal Hom construction,
point pullback and derived-functor constructors locally irreducible, following the
existing derived pullback module. No exported attribute changes. The existing public open
normalization proof uses explicit branch rewriting and direct term conversion
instead of broad simplification; its dependence on disputed uniqueness remains.
The owning purity-map node records the partial reconstruction and diagnosis.

The retained sandbox also contained a repair of the quarantined import closure.
Current server records were checked over SSH: the item claim belongs to A2, the
queue lists two holes and a disputed statement, and the historical build error
reports a missing source. The item and the missing dependency sources have since
been restored on main. Redundant restoration copies and their historical change
record are removed from this packet; no archive or library module is withdrawn.

One repair is still needed in `Sheaf.SixFunctors.IntegralNormalizedFamily`, now
unclaimed. Its newer restored private wrapper produced excessive kernel checking
(previous checks: 76 seconds, with 63.4 seconds in kernel checking; a first
continuation variant took 70 seconds). Move normalization conversion after
selecting the concrete localization witnesses, retaining all four explicit
normalization unfoldings and every public signature. The private witness selector
uses a logical continuation; its unused `selectDiagonalLimit` wrapper disappears.
This changes proof packaging only. All six direct importers are checked unchanged
against this repair and their temporary copies are removed before delivery.

Current single-file checks pass without warnings: the repaired root in 2.0 s,
the diagnostic module in 10.0 s, and the final item in 32.8 s. All six direct root
importers pass against the repair; the remaining contraction check took 11.4 s.
Profiler options are removed. The final packet contains three Lean modules.

Change records:
`coord/changes/A2-smooth-purity-integral-system-and-trace-obstruction.md` and
`coord/changes/A2-integral-normalized-family-kernel-packaging.md`.

## Proved and sorry left

Original holes closed: **0 of 2**. Holes added: **0**. Split off: **0**.
This is partial proof formalization, a proved statement diagnosis, and a dependency
proof-performance repair. It is not a completed smooth-trace definition repair.

Completely proved new private item lemmas:

- `smoothTrace_normalizedIntegralSystem`;
- `smoothTrace_reconstructedInverseSemilinearSquare`;
- `smoothTrace_map_unit_square`;
- `smoothTrace_inverse_reduction_square`;
- `smoothTrace_semilinear_square`;
- `smoothTrace_composite_adjunct_square`;
- `smoothTrace_inverse_comparison_square`;
- `smoothTrace_map_inverse_comparison_square`;
- `smoothTrace_comp_eq_of_map_inv`;
- `smoothTrace_representing_not_unique_at_point`.

The new public `not_existsUnique_representing_trace_at_point` and every helper in
its module are proved. `integralNormalizedFamily_exists` remains completely
proved, with the same dependencies and statement.

The two unchanged item holes, with namespace
`AlgebraicGeometry.ProEtale.CondensedRing`, are:

- `isIso_smoothPurityMap`, node `lem-route-is-iso-smooth-purity-map`;
- `smoothPurityIso_comp_openImmersion`, node
  `lem-route-smooth-purity-iso-comp-open-immersion`.

The imported, pre-existing `existsUnique_smoothTrace` hole remains unchanged. Its
unnormalized uniqueness predicate is false. The existing public open-normalization
proof still uses it and is not counted as new proof progress. No restored
quarantine hole is added by the final packet.

## No longer needed

No module, import, DAG node, or unit step is pruned. All existing proof dependencies
remain planned obligations. The new diagnostic dependency is proved and creates
no further proof item. Mathlib adjunction naturality supplies the categorical
steps, but does not replace the geometric normalization.

The root's private `selectDiagonalLimit` wrapper is unused after conversion at its
sole caller. Redundant sandbox source-restoration copies are not library deletions
and do not count as pruning.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the elaborated `isIso_smoothPurityMap` signature omits
`SmoothOfRelativeDimension d f.left`. The pre-existing positive-dimension point
counterexample certifies the defect. The upstream exception table gives no
permission to change that signature, so it is preserved and remains unproved.

`STATEMENT-DISPUTED`: `existsUnique_smoothTrace` requires only the representing
Hom bijections, without finite-orientation normalization. The new theorem refutes
that uniqueness in the actual geometric-point compact-support Hom spaces. Those
bijections do not determine a pairing. Consequently the existing `smoothTrace`
choice and its open-normalization argument do not construct the finite-normalized
trace required by `def-route-smooth-trace`. The source-library boundary requires
preserving this existing non-theorem body. No arbitrary orientation is introduced
as new data, and no target statement changes.

The restoration claims in the previous sandbox report were historical: current
main already contains those sources. This packet retains only substantive proof
work and the remaining root performance repair. The root and its direct importers
are compiled from current sources before checking the item.

## New nodes

`lem-pur-geometric-point-trace-not-unique`, at
`dag/nodes/sec-smooth-purity/lem-pur-geometric-point-trace-not-unique.json`, attaches
the proved theorem in `Sheaf.SmoothPurity.TraceNonuniqueness`. It records the actual
point sign counterexample, not a replacement purity route or split-off hole. The
owning purity-map node records the diagnostic dependency alongside the retained
reconstruction route. The two change-record paths appear under What changed.

## Related modules compiled before delivery

10 related module(s) compiled against this delivery by deliver3.py: 10 OK.

```json
{"capped": false, "direct": 10, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralNormalizedFamily": "cd3ab9c4cece1ec0e5ee8ce8ef72fffa0f059127", "Sheaf.SmoothPurity.TraceNonuniqueness": "a12f28e35be7fdfafa5a8c0eb7de2b982cc3a3c9", "WeilConjectures.SmoothPurity.Defs": "16fc9fc438b4298af5b3b1550ca9b8555dff2686"}, "results": {"Sheaf.SixFunctors.IntegralKernelContractions": {"hash": "17bfbffcc2e994d2ad929ba87230637d47e5d5ce", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstAmbientFormula": {"hash": "456d1456e7fda7321c8f7c050ee258c1c19647f9", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstContraction": {"hash": "6df44a0fdfe6464a389e88905bace36b87ee6be8", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelFirstTransport": {"hash": "56a3d2f1272a1525fa724b523bcf8d796f55a1cf", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelSecondContraction": {"hash": "9afd502e3a7846b31488050e250cb3ae0856489f", "status": "OK"}, "Sheaf.SixFunctors.IntegralKernelSecondContractionPostcomp": {"hash": "18abbf37005c1fef052a625cc00bff358256e38b", "status": "OK"}, "Sheaf.Targets.SmoothPurityQbar": {"hash": "b61095f4237cc889a88d12105bb9497ef53983af", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.PoincareDuality.Poincare": {"hash": "24c41d940617dccc117d662fe9a0ea621d946970", "status": "OK"}, "WeilConjectures.TraceFormula.Dualizing": {"hash": "6f0205d1db4c599fd319656d4acc1446b3c84ebb", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T09:44:42+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
