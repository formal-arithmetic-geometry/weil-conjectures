## What changed

Replaced the proof hole in `Sheaf.Paper.DiagonalTraceVaryingScalarSquare` with a
construction of the comparison from the supplied restrictions and geometry.
The additive comparison is built from the restrictions' underlying equalities and
ordinary push evaluation, and lifted to a linear comparison using the common
residue action. The horizontal calculation uses the actual finite-unit law and
the system counit. The final comparison is assembled by `NatIso.ofComponents`.
All helpers are private and proved; the statement and public import are unchanged.
Explicit section and additive-map constructors keep coefficient presentations from
being unfolded while checking the horizontal square.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTraceVaryingScalarSquare`
(node `lem-sfb-diagonal-trace-varying-scalar-square`). No holes added or split off;
no sorry remains in the item module. The clean module compiled through
`lcompile.py` in 44.9 seconds; compiling it to a sandbox artifact took 53.4 seconds,
within the 60-second limit. A separate audit importing that sandbox artifact prints
exactly `[propext, Classical.choice, Quot.sound]` for the proved theorem.

## No longer needed

No existing import or module is removed. The proof does not separately use
`lem-coef-semilinear-derived-sections` as a proof dependency: all comparisons here
are ordinary comparisons before localization. Its definition-level use through
the existing geometry interface is preserved. No unit step is bypassed.

Searches: LeanFinder returned scalar restriction and presheaf pushforward
operations, Loogle returned `NatIso.ofComponents` and its component lemmas, and
the Mathlib grep found pushforward defined as precomposition followed by scalar
restriction. None states the normalized varying-system square.

## Where the brief, the DAG or earlier work was wrong

The live server queue identifies this as a one-hole proof item, with no current
build-error entry. The shared snapshot retains an older rework row, so the live
records were checked before work began.

The earlier plan discusses generic underlying comparisons. The current Geometry
also contains the actual finite-unit horizontal law. Using this law together
with the counit gives the horizontal comparison directly, without a new
intermediate statement or a choice of underlying identifications. Level zero,
identity morphisms, zero systems and empty charts require no exceptional case.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceVaryingScalarSquare": "87848f9c6745a6b7c1709b9179106441d66c8f79"}, "results": {"Sheaf.Paper.DiagonalTraceOrdinaryScalars": {"hash": "a59e55fb063cdf40e59fa4a39a4ff7c867ef0770", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T02:51:20+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
