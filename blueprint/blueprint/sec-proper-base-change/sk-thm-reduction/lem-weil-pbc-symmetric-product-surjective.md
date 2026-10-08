+++
id = "lem-weil-pbc-symmetric-product-surjective"
kind = "lemma"
title = "Surjectivity of the symmetric-product morphism"
order = 1202
uses = ["def-weil-pbc-scheme-conventions", "def-weil-pbc-symmetric-product-morphism", "lem-weil-pbc-surjective-nonempty-fibres", "lem-weil-pbc-symmetric-product-finite"]
+++
Let $\sigma_n:(\mathbf P^1_S)^n\to\mathbf P^n_S$ be the symmetric-product
morphism [def-weil-pbc-symmetric-product-morphism]. It is finite and
surjective. Equivalently, over every algebraically closed geometric point of
$S$, every binary form of degree $n$ factors as a product of $n$ linear forms,
including factors at infinity.

## Proof

Over an algebraically closed geometric point, every binary form of degree $n$
factors as a product of $n$ linear forms, so every geometric fibre of the
morphism constructed in [lem-weil-pbc-symmetric-product-finite] is nonempty; a
finite-type morphism with nonempty geometric fibres is surjective
([lem-weil-pbc-surjective-nonempty-fibres]).
