+++
id = "lemma-nagata-diagonal-base-change"
kind = "lemma"
title = "Diagonal commutes with base change"
order = 327
lean = ["CategoryTheory.Limits.diagonal_pullback_fst"]
+++
For $X_\lambda\to S_\lambda$ and $S\to S_\lambda$, the base change of
$\Delta_{X_\lambda/S_\lambda}$ is canonically identified with
$\Delta_{X_\lambda\times_{S_\lambda}S/S}$.

## Proof

Base change the defining fibre square of the diagonal. Associativity of
fibre products identifies the result with the map sending a point to its
pair with itself, which is the diagonal of the base-changed morphism.
