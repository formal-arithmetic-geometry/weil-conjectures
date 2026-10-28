## What changed

Replaced the sorry in AlgebraicGeometry.ProEtale.RationalP1.ambient_twisted_unit_mate directly from
Mathlib CategoryTheory.unit_mateEquiv, naturality of condensedAmbientExchange, functoriality,
the supplied compatibility equation h, and naturality of the f' adjunction unit.
The proved private helper mate_unit_maps performs the categorical calculation.
A private ambientAdjunction wrapper and the proved scalarTwistedUnit_eq and
condensedAmbientExchange_eq API lemmas share the derived structural conversions.
These reduce the compile from a kernel timeout to 15.1 seconds in the profiled check.
No intermediate obligations were introduced. The existing Lean
statement and all public definitions remain identical.

Corrected the statement, statement dependencies, proof, and proof dependencies of
lem-sfb-ambient-twisted-unit-mate to describe its existing Lean attachment. Its old
statement was copied from the unrelated unshifted Tate-line composition obligation.
Both citing nodes still hold: lem-sfb-scalar-component-from-trace uses this precise
ambient mate identity, and lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core
uses the former assembly. The complete correction record is statement_change, and the
change record is coord/changes/E9-ambient-twisted-unit-mate-node.md.

The three prescribed msearch searches were performed: LeanFinder and Loogle both found
unit_mateEquiv; grep confirmed the mate and unit-naturality declarations in Mathlib.

## Proved and sorry left

The complete proof, including all private helpers and the real adjunction wrapper,
compiled through lcompile.py in 15.1 seconds with profiling enabled. Profiling options
were then removed; the final source compiled cleanly in 12.6 seconds after import cleanup.
The current server records independently confirmed the same two citing nodes.

Closed one existing hole:
AlgebraicGeometry.ProEtale.RationalP1.ambient_twisted_unit_mate
(node lem-sfb-ambient-twisted-unit-mate).

Holes added: zero. Holes remaining in this module: zero. Split-off obligations: zero.

## No longer needed

Removed the unused proof import all
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar, and redundant
public imports Sheaf.Paper.DerivedExchangeExactNormalization and
Sheaf.Paper.RationalTatePullback. Both public imports remain transitively re-exported
through RationalP1ScalarChernMaps; no library module is pruned from the import closure.
No new auxiliary modules are needed. No existing module is withdrawn. The old node's
unshifted rational Tate-line composition claim and its dependency on
def-sfb-rational-tate-pullback-comparison are not part of this categorical proof; the
supplied e, e2, and h are all the line-comparison data it needs. The geometric
line-composition theorem used elsewhere is retained. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old node's title, statement, source, and searches described a different lemma;
its Lean declaration record and its parent uses identify the ambient twisted-unit mate.
The statement and proof metadata are repaired here; the title, source, and historical
searches are maintainer-owned fields, so their stale values are reported for correction
by the maintainer. proof_origin and statement_change.source identify the actual
rational P1 triangle source. The unit-mate compatibility is the existing Mathlib leaf
lem-pur-mate-unit-compatibility, rather than any new geometry or Tate-line composition
lemma. No target statement or definition is changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.AmbientTwistedUnitMate": "3655497db20fbccc6afea72facc3914ffb6686f2"}, "results": {"Sheaf.Paper.ScalarComponentFromTrace": {"hash": "2f717160f5d3cd72ff942a9789a9a1682ead6618", "status": "OK"}, "Sheaf.Paper.ScalarP1UnitMateComponent": {"hash": "532c89db1d2eb27a104d3e7c6cbf9d173fdcbc7d", "status": "INFRA"}}, "seconds": 89, "time": "2026-10-28T10:35:33+0800", "transitive": 0, "version": 1}
```

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
