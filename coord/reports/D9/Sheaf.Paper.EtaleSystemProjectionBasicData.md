## What changed

The item theorem now assembles `BasicData` from two strictly simpler existence
statements: a family of ordinary proper/open support presentations and a family of
exact level evaluations on X, Z, and Y. Scalar fields are chosen directly from the
existing normalized `nonempty_systemScalarModel` theorem, with the coefficient-site
universes made explicit. Added the modules
`Sheaf.Paper.EtaleSystemProjectionSupportExistence` and
`Sheaf.Paper.EtaleSystemProjectionEvaluationExistence`, each retaining one unresolved
construction theorem as a named public statement.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjectionBasicData_nonempty`.
The proof compiles and has no `sorry`.

Added two strictly simpler construction obligations, both intentionally left as
named theorem sorries:

- `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjectionSupportData_nonempty`,
  node `lem-pur-etale-system-projection-support-existence`;
- `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjectionEvaluationData_nonempty`,
  node `lem-pur-etale-system-projection-evaluation-existence`.

The scalar fields are fully constructed from
`SheafOfModules.nonempty_systemScalarModel`; no sorry occurs in a definition.

## No longer needed

The item no longer imports or cites the four large construction interfaces directly
in its proof. Their obligations are recorded on the two split nodes: support uses
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-pur-system-level-left-extension`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`; evaluation uses
`lem-coef-semilinear-derived-sections`. The item itself additionally uses
`lem-pur-system-scalar-model`. No unit step is bypassed, and no existing module is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original item bundled three independent ordinary choices into one theorem, while
its proof plan supplied only a prose construction of those choices. The support and
evaluation records are strictly smaller than `BasicData` and are now explicit named
obligations, so the top-level assembly is a real Lean proof rather than a relocated
anonymous `sorry`. The scalar component was already determined by the normalized
system scalar-model existence theorem and did not require a new split.

## New nodes

- `lem-pur-etale-system-projection-support-existence`, implemented by
  `Sheaf.Paper.EtaleSystemProjectionSupportExistence`.
- `lem-pur-etale-system-projection-evaluation-existence`, implemented by
  `Sheaf.Paper.EtaleSystemProjectionEvaluationExistence`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleSystemProjectionBasicData": "ff5af183cfd384032b7b403c883625a4aeec33bc", "Sheaf.Paper.EtaleSystemProjectionEvaluationExistence": "e36d705e348cf4bada15d66dfd69e95dfedf9bb3", "Sheaf.Paper.EtaleSystemProjectionSupportExistence": "be323bfc83350ec4f9b7d6ba6b53b9d981425b32"}, "results": {}, "time": "2026-10-28T03:36:36+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
