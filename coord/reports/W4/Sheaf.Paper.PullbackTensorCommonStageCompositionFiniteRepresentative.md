## What changed

Added the proof-only import `Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation`.
The assigned theorem now chooses a finite representative for the left composite using
`GeneralAlgebraicallyClosedCoefficients.representatives`, then invokes the fixed-stage
square theorem to obtain the right representative with the same stage arrow.

The fixed-stage square is a new public theorem module with a named `sorry`; its statement
is strictly smaller because it assumes the stage, endpoint bounds, representative, and
left-route equality and concludes only the right-route equality.

## Proved and sorry left

Proved `WeilConjectures.commonStageCompositionFiniteRepresentative` (closed 1 of 1
sorries in the assigned module).

Added one split-off sorry:

- `WeilConjectures.commonStageCompositionFiniteRepresentative_stageEquation` in
  `Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation`, node
  `lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation`.

## No longer needed

None. The fixed-stage theorem is the required finite-stage calculation; the existing
rational composition theorem remains its stated proof dependency.

## Where the brief, the DAG or earlier work was wrong

The one-step DAG proof plan omits the substantial fixed-stage expansion and cancellation
needed after choosing a common representative. That calculation is now isolated as a
strictly smaller named theorem. No target statement or existing definition was changed.

## New nodes

`lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation`:
fixed-stage representative square, with source and proof recorded in its node JSON.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation": "88513d8437f5750840c6a135535f048cae1f0ca7", "Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative": "3f0baed801312cc0af5d0874b2fce9b9c548c124"}, "results": {}, "time": "2026-10-28T08:06:04+0800", "transitive": 0, "version": 1}
```

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
