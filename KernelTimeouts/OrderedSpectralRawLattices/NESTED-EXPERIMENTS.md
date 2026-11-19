# OrderedSpectralRawLattices: nested representation audit

Source: `f4946fdb6b6`, `AlgebraicGeometry/Coefficient/OrderedSpectralLattices`,
`small_spectral_raw_lattices`; Lean/Mathlib 4.35.0. All numbers below are
retained measurements from `WORKPLAN-EXPERIMENTS.md`, not new runs. The
linked, unchanged fixtures are in `probes/nd/`. The default heartbeat limit
is 200,000. Kernel-only time and heartbeat consumption were not recorded.

## Original context and A records

The cost site is the final conversion of the inferred type of
`CondensedRing.exists_stratified_lisse_integral_lattice` to the declared
`RawStratifiedLattices` type. The three let-bound values contain two
`Profinite.continuousMapRingObj` constructions and a `Functor.map`; the
predicate contains locally free modules over the resulting ring objects.
The first divergence in each ring-object value is a topology instance path
through `spectralNorm.nontriviallyNormedField` and `IsLocalRing.toNontrivial`:
`Semifield.toCommSemiring` in the inferred type versus
`CommRing.toCommSemiring` in the goal. After both local-ring paths are
disabled, the next difference is `instIsDomain` versus
`IsDomain.of_isSimpleRing` under `Algebra.IsSeparable.of_integral`.

The following are individual A-variant records for the existing
source-availability matrix. Each retains the theorem obligation, the three
let values, and the final conversion. Inference is rerun from source in each
probe; no explicit-instance Kernel replay or synthesis-only timing was made.
Section-10 fields shared by all rows: instance depth and field count are the
unchanged original hierarchy; the consumer uses both ring-object values and
the coefficient map in the lattice predicate. The selected paths and first
divergence are reported in the table and D audit. Explicit instance terms,
synthesis time, Kernel-only time/heartbeats, and a same-term replay are
unavailable. The prior `FinalExact` diagnostic counted 23,580 reducible
`Functor.obj` reductions at the timeout; it does not attribute those
reductions to an individual route.
All checked probes used one Lean thread. `R`, `H`, and `D` mean the regular,
Henselian, and simple-ring/domain instance routes are disabled. The
`probes/nd/` paths link to the original fixtures in `probes/`; no `sorry` or
skipped Kernel is counted as a success.

| ID | Disabled paths | Elaborated first ring values | Kernel result | Wall s | CPU user+sys s | RSS KB | Interpretation |
|---|---|---|---|---:|---:|---:|---|
| A-OS-0 | none | unequal semiring paths | timeout | 40.23 | 46.31+0.99 | 3,341,996 | baseline |
| A-OS-R | R | unequal semiring paths | timeout | 44.93 | 44.15+0.78 | 3,284,440 | single removal insufficient |
| A-OS-H | H | unequal semiring paths | timeout | 45.23 | 44.37+0.85 | 3,285,356 | single removal insufficient |
| A-OS-D | D | unequal semiring paths | timeout | 45.43 | 44.56+0.86 | 3,284,008 | single removal insufficient |
| A-OS-RH | R,H | unequal domain paths | timeout | 45.23 | 44.30+0.88 | 3,284,080 | first difference moves |
| A-OS-RD | R,D | unequal semiring paths | timeout | 45.23 | 44.39+0.82 | 3,283,492 | pair insufficient |
| A-OS-HD | H,D | unequal semiring paths | timeout | 45.53 | 44.60+0.88 | 3,284,536 | pair insufficient |
| A-OS-RHD | R,H,D | both ring values syntactically equal | ok | 10.11 | 13.82+0.92 | 2,564,172 | combined alignment is effective |

The original and all-aligned rows have a same-session baseline in the
workplan. The partial rows come from an earlier fixed-concurrency session,
so their wall times are only used for timeout/success and expression-path
classification. `AllDisabledHead.lean` checks the changed elaborated pair:
the third `Functor.map` value and the folded predicate still differ. The
all-aligned row is a matched *within-case* fast control. It is not an
independent fast declaration for the project-level comparison of section 9.

These rows establish that the source instance bundle controls the observed
cost, but they are not the A/A, B/B, A/B, B/A matrix: the imported helper's
stored type cannot be independently re-elaborated by changing local
priorities. Synthesis time and a replay with explicit instance arguments
remain unavailable. A strict section-3 A completion claim is therefore not
made.

## B and C status

No depth series was measured. A valid B fixture must retain the same final
lattice-predicate conversion while placing the *same* ring-object path
difference under successive data-bearing instance parameters. No fanout
series was measured. A valid C fixture must make every repeated field carry
the actual ring-object or lattice data and force each field in the consumer;
the three competing source instance routes are not themselves three
repeated fields. Neither depth nor field fanout is inferred from the eight
availability rows above. Thus B and C are inconclusive.

## D: representation provenance

| Role | Inferred/helper side | Declared/goal side |
|---|---|---|
| Original declaration | imported `exists_stratified_lisse_integral_lattice` | local `small_spectral_raw_lattices` |
| Construction | imported theorem type, already elaborated | local source re-elaboration of `RawStratifiedLattices` and the three lets |
| Data | `continuousMapRingObj` values, coefficient map, lattice predicate | same mathematical ring objects and lattice predicate |
| Instance path | semiring route via `Semifield.toCommSemiring`; later domain route | `CommRing.toCommSemiring`; `instIsDomain` after R,H are disabled |
| Wrapper/let | expanded quantified predicate under three lets | named `RawStratifiedLattices` under three lets |
| Proof abstraction | no first-divergence evidence | no first-divergence evidence |

First divergence: inside the first `continuousMapRingObj` value, then the
second, below its topology instance; it is a data-bearing instance argument,
not a proof-only field. The producer is local instance synthesis against an
imported type whose instance arguments were fixed earlier. The repeated
appearance in two ring values is observed, but its separate Kernel cost was
not measured. D confidence: strongly supported for this provenance; no
claim about the Kernel's internal reduction order.

**Evidence level:** below section-12 Level 1 under the strict explicit-replay
and independent-provider conditions, despite a strong exact-site
source-availability control. Levels 2 and 3 are not reached.
