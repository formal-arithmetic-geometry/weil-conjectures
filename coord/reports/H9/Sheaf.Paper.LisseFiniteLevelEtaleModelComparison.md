## What changed

Marked `lisse_finite_level_etale_model_comparison` `STATEMENT-DISPUTED` and retained its
original proof hole. The declaration compiles unchanged apart from the diagnostic
comment.

## Proved and sorry left

No theorem was proved. One `sorry` remains in
`AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison`.

## No longer needed

None. The statement's public import of
`Sheaf.Paper.LisseTowerEtaleDescentData` remains necessary for its types and
definitions, and the proof plan's declared dependencies are not used because the
statement is not valid as written.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the hypotheses constrain `E` through `hmodels` and constrain
`D` only by boundedness and finite local constancy; they never relate `D` to `E`.
Taking `E := 0` and `N := 0` makes the local-model premise compatible with the zero
comparison, while a nonzero constant finite locally constant complex concentrated in
degree zero is an admissible `D`. The claimed conclusion would then identify its
fixed realization with zero. The comparison subclaim therefore needs a hypothesis
relating `D` to `E` (or a conclusion quantified over the `D` constructed by the
model-data subclaim) before it can be proved.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleModelComparison": "b3277034a6e5546b86793dc781f915351075aef8"}, "results": {}, "time": "2026-10-28T07:55:22+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
