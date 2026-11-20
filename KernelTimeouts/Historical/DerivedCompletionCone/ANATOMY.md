# DefEq Cost Anatomy: Derived-Completion Cone

Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, source `9ba4d01f55c`.
The `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` import
closure was rebuilt. The patch is `../Anatomy/kernel/lean-v4.33.1.patch`;
the inline and three control probes are in `probes/anatomy/`.
All runs used mimalloc. A three-second run against stale import artifacts
was excluded.

## Root and reproduction

The inline `Cone (quotPowFunctor J I ⋙ tensorLeft K) := sorry` value and
type checks are cheap. Its final inferred/declared type conversion reaches
Lean's deterministic kernel timeout. The installed release reproduced it
in 124.38 s process wall (13,628,268 kB peak RSS), versus 118.66 s in
the earlier historical run. A matched unpatched source run took 115.96 s
(13,607,744 kB RSS); counters took 124.83 s (13,602,116 kB), 7.6% more
process time than source; trace took 150.39 s (14,081,004 kB), 29.7% more.
All three returned the same deterministic timeout. Instrumented root 506
is a process-local serial; declaration and probe identify the operation.

| Control | Release process wall | Counter process wall | Largest counter root | Result |
| --- | ---: | ---: | ---: | --- |
| Named diagram | 2.39 s | 2.15 s | 0.123 ms, 22 calls | completes |
| Explicit shared instance | 2.38 s | 2.13 s | 1.646 ms, 344 calls | completes |
| Named and explicit matrix | 2.49 s | 2.20 s | 1.668 ms, 344 calls | completes |

The controls change representation and do not run the same slow root.
Their largest-root figures are upper bounds over all reported roots, not
paired conversion IDs. The earlier structural diff found 36 outer proof
position differences; it is not a count of expensive Kernel entries.

## Exclusive cost profile

The counter root took 105.142 s:

| Mutually exclusive category | Time | Root share |
| --- | ---: | ---: |
| Recursive comparison outside WHNF | 51.845 s | 49.3% |
| Outer WHNF/reduction | 53.297 s | 50.7% |

The remaining 19.69 s of process wall contains imports, elaboration,
wrapper work, and any unmeasured runtime cost; it is not assigned to GC.
The trace root took 132.702 s (69.479 s comparison, 63.223 s reduction),
kept separate from counter-mode shares. The counter root entered
43,167,510 outer WHNF requests, 25,821,810 Delta unfolds, 24,729,507
Beta, zero Iota, 770,484 Zeta, and 4,248,404 projection steps. Direct
Delta unfolding took 2.147 s inside reduction. Trace head timers show
`Functor.obj` 1,341,824/148.601 ms, `DFunLike.coe`
906,642/161.520 ms, `HAdd.hAdd` 1,171,372/138.584 ms,
`HSMul.hSMul` 864,776/102.744 ms, and `AddSemigroup.toAdd`
1,121,002/89.579 ms (unfolds/direct time). These heads generate
subsequent work, but their direct unfold operations are cheap.

## Tree and proof propositions

The timeout root made 12,220,822 recursive DefEq calls: 12,220,746
successful exits and 76 exception exits, maximum depth 111.
Branch exits include quick 5,535,266, projection 3,115,313,
application 2,133,228, second WHNF 1,053,662, proof irrelevance
187,630, quick-reduced 148,121, and lazy Delta 47,526.
The trace placed 11,738,572 calls in the 64-127 depth bucket.
Fan-out includes 5,574,967 leaves, 4,221,761 one-child calls,
1,122,927 two-child calls, 747,591 three-child calls, and
27,926 calls with 21 children. There were 343,920 Pi-domain
comparisons, 6,537,426 proof attempts, and 187,634 proposition
comparisons.

Trace captured all proposition pairs: 187,634 exact-distinct ordered
expression-node pairs, zero exact repeats, and 187,634 distinct raw
structural hashes. Nested-exclusive proposition-frame times are
diagnostic: they overlap the root comparison/reduction partition.

| Proposition body family | Entries / distinct pairs | Nested-exclusive counter time |
| --- | ---: | ---: |
| Generated `Eq|Eq` | 187,571 / 187,571 | 105.106 s |
| `HasCoproduct` | 37 / 37 | 21.384 ms |
| `Small` | 7 / 7 | 2.331 ms |
| `PreservesColimit` | 5 / 5 | 1.563 ms |
| `IsGrothendieckAbelian` | 2 / 2 | 0.019 ms |
| `HasSheafify` | 1 / 1 | 0.001 ms |
| `IsMonoidal` | 1 / 1 | 0.001 ms |

The trace-mode `Eq|Eq` frame total was 132.657 s. Proof-term head
groups show generated algebraic positions throughout this span:
`instAddHomFunctor._proof_2` 6,731 entries/17.194 s,
`AddCommGroup.add_comm` 83,280/11.879 s,
`LinearMap.instAdd._proof_2` 20,193/11.916 s,
`LinearMap.instAdd._proof_1` 20,193/9.344 s, and
`LinearMap.instSMul._proof_2` 14,214/8.152 s in counters.
The original `inlineCone._proof_1` `HasSheafify` comparison and
`inlineCone._proof_2/_proof_3` Grothendieck comparisons each appeared
once in trace and cost under 0.03 ms as proposition frames. This head
grouping does not identify exactly which of the 36 structural differences
were visited, nor a particular shared concrete instance pair.

Top 20 *individual* trace children by exclusive time follow; the patch
records parent IDs and heads, but not complete field/argument paths.

| Left/right head | Depth | Children | Exclusive ms |
| --- | ---: | ---: | ---: |
| `CategoryTheory.CategoryStruct.comp` | 66 | 6 | 830.572 |
| `Eq` | 88 | 4 | 404.565 |
| `NSMul.nsmul` | 98 | 3 | 369.048 |
| `Add.proj` | 89 | 1 | 357.477 |
| `SMul.smul` | 88 | 3 | 178.002 |
| `SMul.proj` | 89 | 1 | 175.692 |
| `Add.add` | 72 | 3 | 167.590 |
| `HSMul.hSMul` | 78 | 1 | 87.490 |
| `Add.add` | 69 | 3 | 84.048 |
| `DFunLike.coe` | 87 | 2 | 74.975 |
| `AddSemigroup.proj` | 87 | 1 | 41.591 |
| `Add.add` | 82 | 3 | 36.902 |
| `Add.add` | 78 | 3 | 35.658 |
| `AddCommGroup.add_comm` | 72 | 1 | 25.010 |
| `ModuleCat.Hom.hom'` | 74 | 1 | 19.912 |
| `SMul.smul` | 80 | 3 | 18.563 |
| `Add.add` | 87 | 3 | 15.278 |
| `AddCommGroup.add_comm` | 70 | 1 | 14.315 |
| `AddHom.toFun` | 85 | 2 | 8.861 |
| `functorCategoryPreadditive._proof_3` | 61 | 1 | 7.064 |

## Repetition, cache, and memory

The first 5,000,000 general recursive calls contain 3,416,239 distinct
ordered expression-node pairs, 1,583,761 exact repeats, and 2,639,593
raw-expression hash groups. Repeated sampled calls contribute 443.751 ms
immediate exclusive trace time, excluding descendant cost. The success
cache has 2,688,584 hits/14,499,827 misses; the failure cache has
zero hits/74,390 misses. Proposition pairs themselves did not repeat,
even though general recursive pairs did. No local-context fingerprint,
reverse-pair count, repeated-subtree inclusive time, or exact common
instance argument sharing was captured. Raw hashes may collide.

Both named-diagram and explicit-instance controls reduce the observed
slow work to millisecond roots; their small roots also have far fewer
calls, proposition comparisons, and reductions. The experiment cannot
separate their effects on fan-out, instance-pair count, or cost per
comparison within the original root because their roots differ.
Expr allocation, GC time, and phase-specific live memory were not
measured; RSS is only a process proxy. The direct cost signature is
millions of deep comparison/WHNF steps within generated equality proof
propositions, not equal expense across 36 outer proof differences.
