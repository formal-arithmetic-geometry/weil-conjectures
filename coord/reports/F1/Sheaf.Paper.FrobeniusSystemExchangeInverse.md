## What changed

Proves `frobeniusSystemDirect_inverse_evaluation` in
`Sheaf.Paper.FrobeniusSystemExchangeInverse`, without changing its statement.
The proof explicitly constructs the conjugated evaluation of the existing
whole-system isomorphism, identifies its hom using `systemExchange_evaluation`,
and calculates its inverse. Evaluation is not used to detect morphism equality.

Private congruence metaprograms construct kernel-checked equality transports
between categorical argument types, avoiding expensive instance conversion.
Existing isomorphism proofs select standard instances locally, with competing
instance removals scoped to their proof commands. No public imports or data
definitions change. The updated node removes the redundant finite-invertibility
and joint-conservativity route.

The item module compiled alone in 31.4 seconds after cleanup. An ordered
compilation of the item followed by its unchanged direct consumer
`Sheaf.Paper.NativeWeilScalarFrobeniusCounit` passed. The consumer copy was used
only for this check and is excluded from the delivery. The delivery tool performs
the required compile, axiom and preflight checks.

Change record: `coord/changes/F1-frobenius-system-inverse-import.md`.

## Proved and sorry left

Closed one of four original holes:

- `WeilConjectures.FrobeniusExchange.frobeniusSystemDirect_inverse_evaluation`.

No holes were added and no statements were split off. Three original holes remain,
all attached to `lem-weil-frobenius-system-exchange-inverse`:

- `WeilConjectures.FrobeniusExchange.frobeniusSystemCompact_inverse_evaluation`.
- `WeilConjectures.FrobeniusExchange.frobeniusDirectIntegral_inverse`.
- `WeilConjectures.FrobeniusExchange.frobeniusCompactIntegral_inverse`.

The generic cancellation and inverse calculations for the remaining clauses were
investigated, but their native proofs are not delivered as completed proofs.
Their original statements, docstrings and holes remain intact.

## No longer needed

No Lean module is withdrawn and no public or proof import is removed. The proof
route no longer needs `lem-weil-frobenius-finite-exchange-inverse`
(`Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse`): whole-system invertibility
is already proved by equivalences and mates, while the finite inverse is obtained
by conjugating that isomorphism. Its dependency entry and the redundant step
using joint conservativity are removed from this node. Other users of the finite
exchange lemma are unaffected; its module is preserved.

The unit statement and realized unit steps remain unchanged. All scratch
experiments and an unused draft open-exchange split are excluded from delivery.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The old node retained a redundant plan to prove finite
invertibility and then detect system invertibility, after system invertibility
had already been proved by the shorter equivalence/mate route. The updated plan
uses evaluation only to identify the displayed forward and inverse formulas.

Large definitionally equal categorical argument types caused kernel conversion
timeouts. Explicit congruence transports resolve this for the delivered direct
inverse proof, with transparency-respecting elaboration and the normal limits.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
