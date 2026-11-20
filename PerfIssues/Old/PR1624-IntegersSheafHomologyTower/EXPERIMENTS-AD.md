# DefEq Internal Cost Experiments

Case: `PR1624-IntegersSheafHomologyTower`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: decomposition

Root: the complete dependent `Iso.trans` endpoint containing the two
`Functor.comp` endpoints. The selected counters root was 6,598,545 calls,
depth 88, 76.752 s wall, split into 38.767 s comparison and 37.985 s
reduction. The trace root was 89.713 s. It made 21,908,916 WHNF requests
(40.275 s), 12,966,166 Delta unfolds (1.398 s), 274,793 Pi-domain
comparisons, 125,785 proposition comparisons, and 3,342,406 proof attempts.
Pair capture found 3,361,091 distinct exact pairs and 1,638,909 repeats;
repeats contributed 672 ms (1.4%) of comparison-exclusive time. Top children
were `Add.add` (24.015 ms), `NSMul.nsmul` (23.588 ms), `LinearMap.mk`
(11.825 ms), and `LinearMap.instAdd._proof_2` (11.207 ms). The isolated
endpoint conversions were 14,769 and 29,112 ms, while the four corresponding
arguments were 0--8 ms. The full dependent endpoint therefore creates work
absent from isolated argument checks.

## A2 and B status

Single-field replacement was rejected by `Kernel.check`: it changes later
dependent endpoint types. Thus no valid type-preserving A2 or B three-way
provider comparison exists. The recorded aligned whole construction is a
broader control, not a component ablation.

## C: dependent comparison

The dependent endpoint is the required C root. The aligned source control had
456,393 calls, 5.256 s wall, and 2.557/2.700 s comparison/reduction; the
aligned target check was 3.42 s. The 93% call reduction and matching reduction
drop identify dependent endpoint construction as the source of the extra
work, while the near-equal original comparison/reduction split rules out a
reduction-only explanation. Pi and proposition timers are nested and are not
added to exclusive totals.

## Accounting and artifacts

`probes/ad/profile.txt` records the complete endpoint trace, isolated argument
checks, and aligned control. Allocation/GC instrumentation was unavailable;
instrumented RSS is not treated as allocated bytes.
