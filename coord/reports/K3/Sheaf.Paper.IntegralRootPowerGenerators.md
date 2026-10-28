## What changed

Added the proof-only module `Sheaf.Paper.IntegralRootPowerLocalGeneration` and imported it from
`Sheaf.Paper.IntegralRootPowerGenerators`. The original extensionality theorem is now proved by
applying the local-spanning interface and the local-spanning extensionality interface. The two
interfaces are split-off statements with documented proofs and DAG nodes.

## Proved and sorry left

The item theorem `WeilConjectures.integralRootPower_hom_ext` is proved, and so are both
split-off statements in `Sheaf.Paper.IntegralRootPowerLocalGeneration` (reviewer's FIX):

- `WeilConjectures.integralRootPower_local_spanning` (node
  `lem-weil-integral-root-power-generators-local-span`): the recursive family G agrees with a
  private copy of the recursive generator; its span is restriction-stable; local spans are
  descended along the locally surjective sheafification units (scalar extension in degree
  one, presheaf tensor in degree d+2) by the argument of the private
  `generator_locally_span` of `Sheaf.Paper.PositiveRootTensorProduct`, which cannot be
  imported (it lies above the item).
- `WeilConjectures.integralRootPower_hom_ext_of_locallySpans` (node
  `lem-weil-integral-root-power-generators-local-ext`): sheaf separatedness of N on the
  covering sieve and `LinearMap.eqOn_span'`.

No `sorry` is left; `#print axioms` of all three gives propext, Classical.choice, Quot.sound.

## No longer needed

No existing imports or declared proof dependencies were pruned. The proof follows the local
spanning and separatedness route represented by the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled local generation and sheaf extensionality into one theorem without
Lean interfaces for either subargument. The delivery records both as strictly smaller named
statements so the parent proof is complete and the remaining work is independently assignable.

## New nodes

`lem-weil-integral-root-power-generators-local-span` records the covering-sieve submodule-span
statement and is declared in `Sheaf.Paper.IntegralRootPowerLocalGeneration`.

`lem-weil-integral-root-power-generators-local-ext` records the extensionality theorem from a
local-spanning witness and is declared in `Sheaf.Paper.IntegralRootPowerLocalGeneration`.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralRootPowerGenerators": "b41379f4e08448e735cd33e9347f2d4405b9b182", "Sheaf.Paper.IntegralRootPowerLocalGeneration": "b1eb9f40a372668b582fd3312dcc25f33d64e598"}, "results": {"Sheaf.Paper.CanonicalTateArrowNaturality": {"hash": "321c1ee44f590e06623a964e1689ccf2a4ca885d", "status": "OK"}, "Sheaf.Paper.CanonicalTateComparisons": {"hash": "8cb0b5d08221d0eb1eedb6b123f3ba6305fdb079", "status": "OK"}, "Sheaf.Paper.CanonicalTateScalarNaturality": {"hash": "12650e04b1d7196415d35576b93c09425997a1c1", "status": "OK"}, "Sheaf.Paper.FrobeniusCoefficientTwistsCanonical": {"hash": "2376159211b8ee9feb9775907954d31a6d5924ed", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}}, "seconds": 53, "time": "2026-10-28T07:18:08+0800", "transitive": 4, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
