# DefEq Internal Cost Experiments

Case: `NativePullTensor`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`
Instrumentation: READY2-4.35.0 counters and trace builds; source and release baselines.

## A1: decomposition

Root: the two `Exists.choose` application-domain conversions under the original
12 binders, replayed as the `Functor.obj` major-premise pair. The source module
baseline was 272.53 s wall / 7,926,140 KB RSS. The two domain checks were
22,998 ms and 23,068 ms (measured). The selected kernel root (trace root 591)
was 2,685,580 calls, depth 81, 37.507 s trace wall, with 25.373 s exclusive
comparison and 12.134 s exclusive reduction. The counters run was 34.078 s,
22.333/11.746 s comparison/reduction. All calls succeeded.

The trace captured 842,601 distinct exact pairs and 1,842,979 repeats in
2,685,580 calls; repeated entries contributed 2.230 s (8.8%) of exclusive
comparison time. There were 32,060 proposition comparisons, 537,023 proof
attempts, 189,446 application attempts, and 21 Pi-domain comparisons. The
maximum fan-out was 28; the depth histogram peaks around 40--46. Top exclusive
children were `Functor.map` (114.530 ms), `tensor_map_comm` (112.911 ms),
`map_unit_comp_str` (55.699 ms), `Functor.modObjObj` (54.071 ms), and
`Functor.flip._proof_4` (52.721 ms). `Functor.obj` unfolded 516,742 times in
118.290 ms and `Functor.map` 216,960 times in 42.163 ms, so the high counts are
cheap reductions relative to the comparison tree. The READY2 expression
counter is the allocation proxy; RSS is only a process proxy.

## A2: targeted ablation

The measured component is the `Functor.obj` major premise (the concrete
functor construction versus the definitionally equal stored premise). The
type-preserving A/A replacement kept the outer Iso, endpoint, consumer, and
exact result type: 0 ms. Restoring the original direction (B/A) took 11,284 ms;
the same-body regular control was 0 ms while the abbrev/raw controls were
11,251--11,299 ms. This is a valid Level-1 ablation with a reversibility
control. It identifies representation asymmetry at the accessor premise as a
causal contributor, while the remaining parent cost is distributed across the
comparison tree.

## B and C

No valid shared-provider three-way construction exists at this consumer: a
local provider would change the dependent `Exists.choose` telescope or the Iso
endpoint. The attempted synthetic variant was therefore not run. The domain
timers and 21 Pi comparisons establish dependent work, but do not isolate a
separate binder-instantiation cost. This is recorded as invalid rather than
inferred.

## READY2 rerun

The selected trace root is `root=591`. The highest inclusive path prefixes are
`root/binder_domain[0]` (41,488.963 ms), its `argument[3]` functor composition
(22,768.488 ms), its `argument[2]` composition (18,720.237 ms), and the two
`Functor.obj` children below those arguments (22,768.349 and 18,719.998 ms).
The trace root measured 41,488.973 ms wall, with 22,845.095 ms comparison
exclusive and 18,643.878 ms reduction exclusive. The counters rerun measured
22,407.489 ms, split 15,131.398/7,276.091 ms. Reported dependent-
comparison and dependent-reduction timers were 15,389.241/14,662.690 ms
(67.4% of comparison-exclusive for the former); proposition comparison and
reduction timers were 7,455.845/3,981.188 ms and are nested.

READY2 created 97,609,480 C++ expressions (3,325,394,512 bytes). The process
proxy changed RSS/commit by 1,832,189,952 bytes in trace (1,812,332,544 in
counters); these are not allocator totals. `/usr/bin/time` reported 1:28.87
wall and 6,323,668 KB maximum RSS for the trace run.

## Accounting and artifacts

`probes/ad/profile.txt` records the READY2 measured rows and source artifacts. The
trace proposition timer is inclusive and overlaps recursive calls; it is not
added to the exclusive categories. Instrumentation overhead on the validated
fast control was 1.32 s release, 1.48 s counters, 1.42 s trace; on the slow
domain control it was 49.39 s release, 53.79 s counters, 59.81 s trace.
