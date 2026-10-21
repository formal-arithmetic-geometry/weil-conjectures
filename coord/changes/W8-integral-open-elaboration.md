# IntegralOpenDirectImage elaboration commands

## Reason

The complete proof normalizes two scalar adjunctions and large internal module categories.
With the original 200000 heartbeat budget, elaboration stopped with max-heartbeat exhaustion
at the main theorem. The proof compiles in 31.8 seconds with the local 800000 budget.
The static interface scanner also records added set_option commands as visible commands.
No target or existing declaration signature, multiplication, functor, or definition changes.

## Old

The existing file's option commands were:

```lean
set_option autoImplicit false
```

The theorem was preceded directly by its source docstring, with no local heartbeat option.
`reductionPullbackMap` and `integral_open_direct_image` retain their verbatim signatures
and the former retains its complete verbatim body.

## New

The file now has these elaboration commands:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
```

The main theorem has:

```lean
set_option maxHeartbeats 800000 in
-- Normalize the two scalar adjunctions and the internal coefficient module categories.
```

The options permit elaboration of the proof; they add no mathematical assumptions or
public declarations. New mathematical statements live in the two separate new modules
and have their own new DAG nodes. The theorem proof and private helpers are kernel proofs.

## Users

`tools/downstream.py Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage --uses
integral_open_direct_image reductionPullbackMap` reports zero downstream modules. Both
names occur only in the assigned module. This does not justify withdrawal: the unfinished
parent DAG still needs the statement, and the module is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | W8 | Same public signatures and definition; complete assembly proof, elaboration options and proved private helpers. |

No consumer adaptation is necessary. All original public imports remain, and the explicit
unit-route proof imports CartesianCoefficients and IntegralModels are retained.

## Status

landed 20261021T172409-L-3367494 2026-10-21 (merge of deliver/W8/Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage)
