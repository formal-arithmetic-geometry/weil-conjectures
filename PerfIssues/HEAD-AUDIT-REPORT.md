# Kernel-bound Head Audits

Scope: `Current/NativePullTensor` and old PR cases #1556, #1563, #1624,
#1625, #1627, and #2122 on Lean 4.35.0 at master revision
`1ef1fddac73e`. Probes replay original stored expressions with ordinary
Kernel checking. [EXPERIMENTS.md](EXPERIMENTS.md) records measured variants
using the guide's shared columns. In the table, a head verdict states the
measured comparison boundary, not a claim that the Kernel took a particular
internal branch.

| Case | Head pair at localized conversion | Head verdict | Supported hypotheses | Necessary vs unfavorable | Evidence level |
|---|---|---|---|---|---|
| [NativePullTensor](Current/NativePullTensor/HEAD-AUDIT.md) | `Iso`/`Iso` endpoints; nested `Functor.obj`/`Functor.obj` | Same heads; `abbrev` field access on different functor major premises costs about 11 s per endpoint | H1, H2, H3, H4 | Unfavorable accessor/major-premise path | Confirmed causal factors |
| [PR #1556](Old/PR1556-AmbientCounterexampleCoproducts/HEAD-AUDIT.md) | `congr` argument-7 `Eq` domain; left `CategoryStruct.comp`; nested `NatTrans.app`/`NatTrans.app` | Proposition comparison 50.090 s; aligning one accessor major premise changes 49.548 s to 0 ms | H2, H3, H4, H6 | Unfavorable projection path strongly supported | Strongly supported |
| [PR #1563](Old/PR1563-RawModuleScalarPullback/HEAD-AUDIT.md) | `Eq`/`Eq` proposition domains; right `CategoryStruct.comp`/`CategoryStruct.comp` | Same head; several concrete arguments cost seconds, nested composition 22.155 s | H2, H4, H6 | Unresolved | Plausible causal mechanism |
| [PR #1624](Old/PR1624-IntegersSheafHomologyTower/HEAD-AUDIT.md) | `Iso`/`Iso` final binder domain; `Functor.comp`/`Functor.comp` endpoints | Same regular head, but four corresponding endpoint arguments compare unequal; whole endpoints compare equal in 14.706/28.640 s | H2, H4 | Necessary unfolding for the concrete compositions; later path unresolved | Strongly supported |
| [PR #1625](Old/PR1625-TensorSheaf/HEAD-AUDIT.md) | `Eq`/`Eq` left `CategoryStruct.comp`; nested `NatTrans.app`/`NatTrans.app` | Same heads; one major premise accounts for roughly 96 s | H2, H3 | Unfavorable projection path strongly supported; inner necessity unresolved | Strongly supported |
| [PR #1627](Old/PR1627-WeilSheafTransport/HEAD-AUDIT.md) | Generated law's `id` proof-argument proposition domain | Same `id` head; instantiated dependent proof domain takes 7.508/33.863 s | H2, H4, H6 | Unresolved | Plausible inner cause |
| [PR #2122](Old/PR2122-DiagonalTraceFiniteEtaleIntegralBoundary/HEAD-AUDIT.md) | Stored value check under `Exists.casesOn` branch | Expensive inner pair not isolated | H8 (phase only) | Unresolved | Unclassified |

## Observations

The native, #1556, #1625, and #1563 probes preserve the original
inferred/expected expression pairs and time corresponding arguments.
Native, #1556, and #1625
also replace one definitionally equal major premise, Kernel-check the
replacement, and observe that the expensive comparison becomes immediate.
Native additionally compares a same-body regular definition with an
`abbrev`: regular/regular takes 0 ms, while abbrev/abbrev takes 11.251 s.

At #1627 and #1563, the costly site is an application argument's
instantiated expected proposition domain. In #1556, the measured domains
at the enclosing `Exists.intro`, `id`, and `Eq.mp` applications are cheap;
the cost descends through their proof values to a 50.090-second `congr`
proof-proposition domain. The generated #1627 proof types
and #1563 theorem's final type are cheap or structurally identical; their
value checks contain the cost. #1625 is the reverse split: its stored value
rechecks in 335 ms and its final inferred/declared type conversion takes
95.520 s. At #1624, independent comparisons of four corresponding
`Functor.comp` endpoint arguments return unequal while the complete
endpoints are equal after 14.706/28.640 s. These splits are direct
measurements, so a whole-declaration timing alone cannot identify the
conversion site.

## Interpretations and limits

The [Lean 4.35.0 Kernel source](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
supports predicting an argument comparison for equal regular-definition
heads and hint-guided lazy unfolding. The native same-body hint matrix and
the three major-premise alignment controls support an unfavorable path
through concrete field accessors. They do not trace the Kernel's exact
reduction sequence. #1624 needs unfolding in its original concrete
representation because same-head argument congruence fails. At #1563
and #1627, the next nested differing term is still needed to choose
between necessary unfolding and a missed cheap comparison. For #2122,
source-level category/functor differences are only
candidates until a timed inner conversion pair is extracted.

This corpus keeps reducibility hints, projection major premises, dependent
domains, proof proposition types, and stored instance arguments as distinct
experimental factors. A shared outer head is a starting point: each case
requires the elaborated argument terms and the expected domain after prior
arguments have been substituted. Counts of downstream unfolds and a faster
replacement proof do not, by themselves, identify the first Kernel
decision.
