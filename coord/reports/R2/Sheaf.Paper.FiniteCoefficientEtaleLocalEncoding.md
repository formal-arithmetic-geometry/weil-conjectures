## What changed

Added two strictly simpler split statements and imported them into
`Sheaf.Paper.FiniteCoefficientEtaleLocalEncoding`. The target theorem now combines
the forward and reverse local-model transport lemmas by a real `constructor` proof.
The split theorem bodies remain `sorry` for follow-up workers; no definition was
changed.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding`
is reduced to the two named directional statements. Two split-off sorries remain:
`finiteCoefficient_etaleLocal_encoding_forward` and
`finiteCoefficient_etaleLocal_encoding_reverse`, with the corresponding DAG nodes.

## No longer needed

No imports or declared proof dependencies were pruned; both directions use the
slice restriction and local-model comparison APIs named in the original plan.

## Where the brief, the DAG or earlier work was wrong

The original item had a page-sized proof plan but no existing theorem expressing
its two directional transports. Splitting exactly those directions is necessary to
state the remaining work as independent, strictly simpler obligations.

## New nodes

`lem-weil-pbc-finite-coefficient-etale-local-encoding-forward` and
`lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse` are the two
split-off directional local-model transport statements.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
