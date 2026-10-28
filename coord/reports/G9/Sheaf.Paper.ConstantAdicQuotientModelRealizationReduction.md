## What changed

The target theorem is now a real composition of a coefficient-only scalar-realization
comparison, the supplied upper model isomorphism transported by derived scalar extension,
and the pulled-back consecutive tower transition.  These two strictly smaller substeps are
declared in `ConstantAdicQuotientRealizationScalarReduction.lean` and
`ConstantAdicQuotientRealizationTowerTransition.lean`; the target imports them proof-only.
The target statement is unchanged.  The three delivered modules compile in import order.

## Proved and sorry left

`AlgebraicGeometry.Scheme.constantAdicQuotient_model_realization_reduction` is proved by
the explicit three-isomorphism composition.

Two strictly smaller named statements remain as split-off sorries:

- `AlgebraicGeometry.Scheme.constantAdicQuotient_realization_scalar_reduction`, node
  `lem-weil-pbc-constant-adic-quotient-realization-scalar-reduction`;
- `AlgebraicGeometry.Scheme.adicTowerPullback_consecutive_transition_iso`, node
  `lem-weil-pbc-constant-adic-quotient-realization-tower-transition`.

## No longer needed

No existing proof dependency or import was pruned.  The original statement dependencies
remain recorded on the target node; its proof dependencies are the two new substep nodes.

## Where the brief, the DAG or earlier work was wrong

The imported one-step plan bundled the coefficient scalar comparison and the pulled-back
tower normalization into the realization transport.  Exposing those two genuinely smaller
interfaces makes the parent proof a concrete categorical composition while preserving the
unit route and target statement.

## New nodes

`lem-weil-pbc-constant-adic-quotient-realization-scalar-reduction` records the coefficient-only
comparison between lower realization of the algebraic derived scalar extension and derived
scalar extension of the upper realization.

`lem-weil-pbc-constant-adic-quotient-realization-tower-transition` records the pulled-back
consecutive normalization of an `AdicTower`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantAdicQuotientModelRealizationReduction": "77cdc9a90937beacc8fbeecd294a581676f3f98a", "Sheaf.Paper.ConstantAdicQuotientRealizationScalarReduction": "d3f30acd7349022b42f87ee1b21a65c450be291f", "Sheaf.Paper.ConstantAdicQuotientRealizationTowerTransition": "b2dc8787ff1e0192cece5d637e98a55859e55228"}, "results": {}, "time": "2026-10-28T08:15:42+0800", "transitive": 0, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
