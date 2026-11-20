# DefEq Cost Anatomy: Slow Derived Tensor

Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, source `bdab171985a`.
The `WeilConjectures.SixFunctors.Etale.Derived.Tensor` import closure was rebuilt.
The observational patch is `../Anatomy/kernel/lean-v4.33.1.patch`; probes
are in `probes/anatomy/`. All runs used the release allocator (mimalloc).

## Root and controls

The root is the inferred/declared type comparison for the standalone
`MonoidalCategoryStruct.tensorObj` pair. Application argument 2 compares
concrete `MonoidalCategory` instances (`inferInstance` on both sides);
arguments 0 and 1 took about 1 ms each. On the installed release, the
standalone pair took 53.184 s and the isolated instance argument 55.046 s
in `instance.lean`. The full `IsLeftDerivedFunctor₂` consumer took
136.595 s forward and 147.988 s reverse. All returned true. Different
scope and sequential order make these times unsuitable for subtraction.

In matched `argument2.lean` runs, the installed release call took 45.833 s
(48.20 s process wall, 7,017,612 kB RSS); unpatched source took 45.046 s
(47.42 s, 7,012,448 kB). Counters took 47.834 s (50.19 s, 7,011,220 kB),
a 6.2% call overhead against source. Trace took 58.528 s (60.98 s,
7,436,328 kB), a 29.9% overhead. Counter timing is used for quantitative
shares and trace for tree shape. The fixed `@[reducible] def` revision
`428569e1ce1` was also rebuilt on its targeted import closure and run
directly with `standalone.lean` in this batch. Its full consumer took
3 ms forward and 2 ms reverse, while the standalone pair still took
46.245 s forward and 51.041 s reverse; application argument 2 took
52.535 s. The control avoids demanding the slow pair in the consumer
without making the pair itself cheap.

## Exclusive cost profile

The counter root (`is_def_eq_core`, process-local root 170) took 42.025 s:

| Mutually exclusive category | Time | Root share |
| --- | ---: | ---: |
| Recursive comparison outside WHNF | 22.844 s | 54.4% |
| Outer WHNF/reduction | 19.182 s | 45.6% |

The 5.809 s between the root span and Lean-level `Kernel.isDefEq` call
is outside this patch's recursive timer and remains unassigned. The trace
root was 54.145 s: 32.429 s comparison and 21.716 s reduction. Its times
are not combined with counter times.

There were 18,804,316 outer WHNF requests, 10,639,573 Delta unfolds,
9,414,298 Beta, 10 Iota, 209,669 Zeta, and 1,409,880 projection steps.
Direct Delta unfolding took 0.846 s within the 19.182 s reduction span.
Trace head timers show `Functor.obj` 661,856/80.476 ms,
`AddGroup.toSubNegMonoid` 747,264/62.526 ms, `Preadditive.homGroup`
715,008/57.804 ms, `NatTrans.app` 545,164/57.197 ms, and
`AddCommGroup.toAddGroup` 677,376/50.099 ms (unfolds/direct time).
Their high counts do not imply expensive direct Delta operations.

## Comparison tree and dependent work

The root made 6,269,622 successful recursive DefEq calls at maximum
depth 96. Branch exits: quick 3,364,397, application 1,264,606,
projection 1,103,968, second WHNF 310,464, lazy Delta 146,897, and
proof irrelevance 79,290. The trace put 5,268,276 calls in the 64-127
depth bucket; fan-out includes 3,360,946 leaves, 1,492,639 one-child
calls, and 551,577 two-child calls. It is deep and broad. There were
46,522 Pi-domain comparisons, 2,905,225 proof attempts, and 79,290
proposition-type comparisons.

Top 20 individual trace children by exclusive time follow. The known
outer path is `tensorObj` argument 2; child IDs and heads do not map
deeper calls to complete structure-field paths. Each row is one call,
not a head-family sum.

| Left/right head | Depth | Children | Exclusive ms |
| --- | ---: | ---: | ---: |
| `CategoryTheory.instNegHomFunctor` | 66 | 7 | 345.334 |
| `AddCommGroup.proj` | 85 | 1 | 333.453 |
| `Add.proj` | 76 | 1 | 166.595 |
| `CategoryTheory.Functor.map` | 68 | 4 | 163.164 |
| `NSMul.nsmul` | 74 | 3 | 156.171 |
| `CategoryTheory.Functor.obj` | 70 | 2 | 81.461 |
| `CategoryTheory.Functor.obj` | 73 | 2 | 78.509 |
| `SubNegMonoid.proj` | 79 | 1 | 73.807 |
| `Quiver.Hom` | 75 | 3 | 36.646 |
| `AddCommGroup.proj` | 80 | 1 | 36.306 |
| `CategoryTheory.Functor.map` | 77 | 4 | 28.519 |
| `SubtractionCommMonoid.toSubtractionMonoid` | 75 | 2 | 16.089 |
| `SubNegMonoid.proj` | 58 | 1 | 15.648 |
| `CategoryTheory.NatTrans.app` | 61 | 2 | 12.835 |
| `CategoryTheory.instAddHomFunctor._proof_2` | 63 | 1 | 6.900 |
| `CategoryTheory.functorCategoryPreadditive._proof_14` | 59 | 1 | 6.807 |
| `CategoryTheory.Preadditive.proj` | 68 | 3 | 5.803 |
| `Function.Injective.subNegMonoid` | 59 | 10 | 4.549 |
| `CategoryTheory.Preadditive.fullSubcategory._proof_6` | 58 | 1 | 3.279 |
| `CategoryTheory.instAddHomFunctor._proof_2` | 67 | 1 | 2.899 |

The nested-exclusive proposition diagnostic is dominated by `Eq|Eq`:
79,031 entries and 41.930 s in counters (54.025 s in trace).
`HasCoproduct` has 130 entries/73.075 ms and `Small` 114/9.129 ms.
Trace proof-term groups include `instAddHomFunctor._proof_2`
24,192 entries/17.881 s, `functorCategoryPreadditive._proof_4`
9,856/4.306 s, and `._proof_1` 7,168/3.374 s. These spans overlap
the root comparison/reduction partition. The timer cannot isolate time
before proof irrelevance completes.

## Repetition, cache, and memory

The first 5,000,000 calls contain 3,333,872 distinct ordered expression
node pairs, 1,666,128 exact repeats, and 2,513,274 raw-expression hash
groups. Captured repeated calls had 266.528 ms immediate exclusive
time, excluding descendants. All 79,290 proposition pairs were exact
distinct; 79,284 had distinct raw structural hashes. The success cache
had 1,438,292 hits/6,296,266 misses; the failure cache had zero hits
and 116,384 misses. Capture lacks local-context identity, reverse-pair
counts, and repeated-subtree cost; raw hashes may collide.

RSS is a process proxy, not Expr allocation or live bytes. Expr
allocations, GC time, and phase-specific memory were not measured.
The instance pair is the only slow application argument of the
standalone parent, but its exact timed field path inside the full
consumer is unobserved. Internally it is a mixed comparison/reduction
tree largely traversed while checking generated equality propositions;
the prominent Delta heads are cheap direct unfolds.
