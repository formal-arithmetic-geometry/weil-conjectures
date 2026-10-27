# scalar-q-splitting-inverse-components

## Reason

The target proof exposes the transport step as two one-sided inverse statements.
The public declarations are needed by the target module and by its parent splitting
statement.

## Old

`scalar_q_chern_splitting` was declared with the displayed scalar Q biproduct
isomorphism conclusion and a `sorry` proof. No inverse-component declarations
were present.

## New

`scalar_q_chern_splitting` has a categorical proof combining the named right and
left inverse equations. The new declarations are
`scalar_q_chern_right_inverse` and `scalar_q_chern_left_inverse`, each preserving
the original hypotheses and stating one side of the inverse equation for the same
explicit scalar Q biproduct map.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RationalP1ScalarChernSplittings | unclaimed | imports the item theorem; its statement and use remain unchanged |
| Sheaf.Paper.RationalP1ScalarChernQSplitting | J3 | uses both new inverse-component declarations in the proof |

## Status

landed 20261027T210055-L-1653112 2026-10-27 (merge of deliver/J3/Sheaf.Paper.RationalP1ScalarChernQSplitting)
