# arithmeticLiftFibrePath proof imports and exact-sequence lemma

## Reason

The proof requires the adopted source theorem that any two fibre functors on a Galois
category are isomorphic, and a new strictly smaller arithmetic exact-sequence theorem.
The item’s proof-only imports and the new public theorem are therefore visible to
consumers. Existing target and helper signatures are unchanged.

## Old

The item had no proof import for the source fibre-functor isomorphism and its arithmetic
exact-sequence clause was part of the item’s single proof hole.

## New

The item privately imports `WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability`
and publicly imports the new `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticExactSequence`
module. The new module declares
`AlgebraicGeometry.Scheme.FiniteEtale.arithmetic_exactSequence`, with one documented
source proof hole and its own DAG node.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath | D6 | uses the exact-sequence declaration and source fibre-functor isomorphism |

## Status

landed 20261020T211654-L-3486977 2026-10-20 (merge of deliver/D6/Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath)
