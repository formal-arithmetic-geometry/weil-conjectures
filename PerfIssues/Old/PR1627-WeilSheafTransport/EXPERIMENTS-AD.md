# DefEq Internal Cost Experiments

Case: `PR1627-WeilSheafTransport`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: decomposition

Roots: the three generated `powFunctor` law fields and the two dependent
`id`-domain conversions. The largest counters root was 10,904,899 calls,
depth 61, 40.808 s wall, split into 20.611 s comparison and 20.198 s
reduction. The trace was 47.557 s, with 25.678/21.879 s comparison/reduction.
The largest root made 7,231,443 WHNF requests (21.879 s), 2,539,771 Delta
unfolds (278 ms), 3,726 proposition comparisons, and 3,500,726 proof attempts;
it had no Pi-domain events because the expensive domain is a proposition
argument inside an application. The bounded pair sample had 1,844,240
distinct exact pairs and 3,155,760 repeats; repeated entries contributed
2.865 s (11.2%) of comparison-exclusive time. Proposition pairs were 2,486
distinct and 1,240 repeated. Other generated-field roots were 19.088 s and
17.225 s with 4,696,766 calls each. The release field checks were 27.8, 55.3,
and 14.6 s; the two id-domain checks were 7,608 and 32,992 ms.

## READY2 rerun

The selected root is `root=1539` in the generated proof-prefix probe. Its
largest path prefixes are the repeated `CategoryTheory.Endofunctor.Algebra.a`
field chain (9,560.060 ms), the two `frobeniusPullback` branches (5,566.976
and 3,992.835 ms), and their `Functor.obj` field bodies (2,626.391 and
2,521.274 ms). The trace root measured 40,765.536 ms wall, with 23,911.980
ms comparison exclusive and 16,853.556 ms reduction exclusive. Counters
measured 29,196.986 ms, split 15,743.540/13,453.445 ms. Dependent
comparison/reduction timers were 23,551.972/16,685.180 ms (98.5% of
comparison-exclusive); proposition comparison/reduction were 359.976/168.376
ms and are nested.

READY2 created 151,676,221 C++ expressions (5,085,228,440 bytes). RSS/commit
delta was 16,711,680 bytes in trace and zero in counters. `/usr/bin/time`
reported 5:31.14 wall and 8,750,504 KB maximum RSS for the trace run.

## A2 and B

The measured component is the dependent proposition passed to `id`, shared in
shape by two generated fields. A type-preserving local abstraction of one
field's proof/data bundle could not be constructed: changing it changes the
dependent domain of the next argument. The generic `IsoAlgebra.liftOfStr`
control removes the generated checks, but changes the construction boundary
and is not a valid A2 or B provider-sharing result. B therefore has no valid
three-way variant and is explicitly not forced.

## C: dependent comparison

The two id domains are the required in-situ dependent probes. Their distinct
7.608/32.992 s costs and the shared proposition/application shape show that
generated fields revisit the same kind of dependent comparison, but the
non-monotone three-field costs show that field count is not a cost model. The
aligned generic-helper source emitted no root above 100 ms, so it is a matched
construction control only. Proof-position timing is nested; no exclusive
proof-type share is claimed.

## Accounting and artifacts

`probes/ad/profile.txt` records per-field and id-domain measurements and the
selected trace. Original source RSS was 7,792,432 KB; aligned source RSS was
1,841,708 KB. Allocation/GC counters were unavailable, so the RSS change is
not attributed to allocation.
