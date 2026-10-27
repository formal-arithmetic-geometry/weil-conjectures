## What changed

The assigned theorem now chooses a projection theory using
`etaleSystemProjectionTheory_nonempty`, obtains a cofinal repetition/support package,
and assembles the factor and evaluation fields into `CofinalBlockEvaluation`.

Two strictly smaller construction statements were added in separate modules:
`EtaleCofinalRepeatSupportExistence` supplies `CofinalRepeatSupport`, and
`EtaleCofinalFactorEvaluation` supplies the two factors, the two evaluation
isomorphism families, and the three displayed evaluation equations. The assigned
module imports these proof-only interfaces and contains no `sorry`.

## Proved and sorry left

The original theorem
`AlgebraicGeometry.Etale.SystemProjection.etaleCofinalBlockFactorization` is proved.

The delivery adds two named lower construction holes:

- `etaleCofinalRepeatSupport_nonempty`, node
  `lem-pur-etale-cofinal-repeat-support-existence`;
- `etaleCofinalFactorEvaluation_nonempty`, node
  `lem-pur-etale-cofinal-factor-evaluation`.

There are no holed definitions and no other `sorry`s were added.

## No longer needed

No mathematical node is pruned. The original block, semilinear, selected-extension,
level-extension and K-flat dependencies are now dependencies of the two split-off
construction nodes, while the assigned theorem directly needs only projection
existence and those two interfaces.

## Where the brief, the DAG or earlier work was wrong

The DAG's single proof step combines three independent geometric constructions whose
full implementations are not present in one existing declaration. The delivery keeps
the stated theorem unchanged and records the repetition package and the factor/evaluation
package as strictly smaller statements, then proves the assembly by ordinary existential
elimination and structure construction. No unit statement or target statement is changed.

## New nodes

`lem-pur-etale-cofinal-repeat-support-existence` records existence of the geometric
repetition/support package for fixed projection, coefficients and cofinal map.

`lem-pur-etale-cofinal-factor-evaluation` records existence of the factors and explicit
evaluation diagrams after the repetition/support package is fixed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleCofinalBlockFactorization": "da10002a4123b1278d0d9534b3b1321e5cba9777", "Sheaf.Paper.EtaleCofinalFactorEvaluation": "fddeae4e55f4f712a319661e51fe9c0744ff7fab", "Sheaf.Paper.EtaleCofinalRepeatSupportExistence": "7c61e536e2f56e9190538df51ec9177e0c96c1f0"}, "results": {}, "time": "2026-10-28T03:30:37+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
