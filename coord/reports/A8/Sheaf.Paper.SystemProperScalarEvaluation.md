## What changed

Proved `systemDirectScalar_finiteEvaluation` by applying the normalized
`SemilinearSections.evaluation_mate` theorem to the system adjunctions and the
intrinsic finite pullback/direct-image adjunctions.  The two evaluation records
are built from `systemPullEvaluation` and `systemDirectFiniteEvaluation`; the
finite square is the inverse mate of `finiteDirectScalar`.  The remaining
scalar/pullback compatibility clause is imported from the split module below.

## Proved and sorry left

Closed the `systemDirectScalar_finiteEvaluation` sorry (1 of 1 item holes).
Added one strictly smaller theorem, whose proof remains `sorry`:
`systemProperScalarEvaluation_compatibility` in
`Sheaf.Paper.SystemProperScalarEvaluationCompatibility`.

## No longer needed

None.  The two original public imports remain needed by the mate construction.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof step bundled the evaluated scalar/pullback compatibility
square together with the mate calculation.  The compatibility equation is now a
separate, strictly smaller split node; the parent node's proof dependencies were
updated accordingly.

## New nodes

`lem-sf-system-proper-scalar-evaluation-compatibility`, implemented by
`Sheaf.Paper.SystemProperScalarEvaluationCompatibility`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemProperScalarEvaluation": "99daba70061029e4019e2a36d43274002eaf26f6", "Sheaf.Paper.SystemProperScalarEvaluationCompatibility": "b655e751cf8fdf77b89111f529f6c002cdf95422"}, "results": {"Sheaf.Paper.CompactSupportScalarEvaluationSquare": {"hash": "4873c6b3e3219cb09a4e30281962b19eb1d15711", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T03:56:21+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
