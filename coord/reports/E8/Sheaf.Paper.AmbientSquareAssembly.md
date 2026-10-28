## What changed

Proved AlgebraicGeometry.ProEtale.RationalP1.ambient_square_assembly in
Sheaf.Paper.AmbientSquareAssembly. A fully proved private helper expands the
composite natural isomorphism, applies the three leg equations, and cancels
an inverse against its isomorphism. The public theorem specializes it to the
canonical derived pullback compositors and transport along the square equality.

Re-expressed the statement using the existing QuotientChange.Modules, L and
scalarPullbackComposition. The conclusion writes out the defining composite of
scalarPullbackSquare. These definitions expand to the original module categories,
derived pullbacks, compositors and condensedAmbientPullbackComparison; explicit
nested source ascriptions preserve the same map composites. All mathematical
objects, binders, maps, hypotheses and conclusion are preserved. No target or
shared definition changes; transparency controls stay enabled.

Replaced the old four imports with the single public import
Sheaf.Paper.ScalarPullbackSquareCoherence, needed for the typed definitions.
Its coherence theorem is not used by the proof.

Corrected lem-sfb-ambient-square-assembly's copied prose and proof plan to match
its existing mathematical Lean interface. Updated lean.statement to the new
spelling, with a statement_change record checking both citers. The full change
record is coord/changes/E8-ambient-square-assembly-node.md.

## Proved and sorry left

Closed 1 of 1 holes:
AlgebraicGeometry.ProEtale.RationalP1.ambient_square_assembly
(blueprint: lem-sfb-ambient-square-assembly).

The private helper assemble_from_leg_equations is fully proved.
Holes added: 0. Split-off statements: 0. Sorries left in the item: 0.
The proof uses only canonical definitions and Mathlib category identities.

The complete proof compiled cleanly in 3.1 seconds with all debugging options
removed. Both direct importers compiled unchanged against it: ShiftedLineSquare
in 6.1 seconds and ScalarP1UnitMateComponent in 7.9 seconds. The compiler used its
private overlay for newer unpublished dependencies. Temporary unchanged consumer
copies were removed before delivery.

## No longer needed

Removed direct public imports Sheaf.Paper.DerivedExchangeExactNormalization,
Sheaf.Paper.CondensedAmbientExchange and Sheaf.Paper.RationalTatePullback,
and the private all-import of
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar.
CondensedAmbientExchange remains available transitively for the canonical data.
No Tate-line functoriality, exact single-complex normalization, shift
compatibility, trace geometry or adjunction mate calculation is used by this
proof. In particular the node's old dependency
def-sfb-rational-tate-pullback-comparison is not needed for assembly. Its
geometric obligations remain in the parents and in the separate Tate-line
composition lemma; no other node or module is withdrawn.

No whole-library module pruning is claimed. Both direct importers retain the
old public imports through RationalP1ScalarChernMaps.

## Where the brief, the DAG or earlier work was wrong

The node statement of lem-sfb-ambient-square-assembly duplicated
lem-sfb-rational-tate-line-comparison-composition word for word, whereas its
Lean attachment and docstring stated categorical square assembly from supplied
leg equations. The corrected prose follows that existing mathematical statement.
Both citing nodes, lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core
and lem-sfb-scalar-component-from-trace, retain the same assembly step.
The geometric composition obligation remains separately stated in
Sheaf.Paper.RationalTateLineComposition.

The copied node title and original source are maintainer-owned fields and remain
in place; they should be aligned with the corrected categorical statement.
The proof origin and statement-change source cite the current blueprint's second
rational P1 triangle and its canonical-map compatibility calculation.

Repeated unfolding of the derived-functor spelling caused tensor-instance
synthesis failures or deterministic kernel timeouts. The existing typed aliases
and explicit defining composite eliminate those conversions without weakening
the statement, changing shared definitions, or adding assumptions.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.AmbientSquareAssembly": "30d40fe14aca9252e927df6d797643bec52c315d"}, "results": {"Sheaf.Paper.ScalarP1UnitMateComponent": {"hash": "532c89db1d2eb27a104d3e7c6cbf9d173fdcbc7d", "status": "OK"}, "Sheaf.Paper.ShiftedLineSquare": {"hash": "9508681127a078b0ebd580718d97df56723a02d1", "status": "OK"}}, "seconds": 61, "time": "2026-10-28T11:41:35+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
