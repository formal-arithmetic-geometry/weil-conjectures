+++
id = "lem-pc-pic-of-field"
kind = "lemma"
title = "$\\operatorname{Pic}$ of a field"
order = 802
uses = ["def-pc-scheme", "def-sc-invertible-module", "def-sc-picard-group"]
+++
Let $k$ be a field. Then the
Picard group of $\operatorname{Spec}(k)$ is trivial:
every invertible $\mathcal{O}_k$-module is isomorphic to $\mathcal{O}_k$.

## Proof

An invertible $\mathcal{O}_k$-module is locally free of rank $1$; an $\mathcal{O}_k$-module
is the same as a $k$-vector space, and a locally free rank $1$ $k$-module
is free of rank $1$ (a module over a field is free; every nonzero
element of a basis is a basis), hence isomorphic to $k=\Gamma(\operatorname{Spec} k,\mathcal{O})$.
