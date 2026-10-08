+++
id = "lem-galois-aut-profinite"
kind = "lemma"
title = "$\\operatorname{Aut}(F)$ is profinite"
order = 969
uses = ["def-galois-category", "def-galois-fibre-functor"]
+++
Let $\mathcal C$ be a category and $F:\mathcal C\to\mathbf{Sets}$ a
functor. Then the evaluation embedding identifies
$\operatorname{Aut}(F)$ with a closed subgroup of
$\prod_X\operatorname{Aut}(F(X))$. Consequently, if all $F(X)$ are
finite, then $\operatorname{Aut}(F)$ is profinite.

## Proof

Let $\operatorname{Aut}(F)\subseteq\prod_X\operatorname{Aut}(F(X))$
carry the topology induced from the product of the discrete topologies,
as in [def-galois-category], and let $\xi=(\gamma_X)$ be an
element of the product not induced by a natural
automorphism. Then there are $f:X\to X'$ and $x\in F(X)$ with
$F(f)(\gamma_X(x))\neq\gamma_{X'}(F(f)(x))$. The open subsets
$U=\{\gamma:\gamma(x)=\gamma_X(x)\}\subseteq\operatorname{Aut}(F(X))$ and
$U'=\{\gamma':\gamma'(F(f)(x))=\gamma_{X'}(F(f)(x))\} \subseteq\operatorname{Aut}(F(X'))$ give the open neighbourhood
$U\times U'\times\prod_{X''\neq X,X'}\operatorname{Aut}(F(X''))$ of
$\xi$, which misses $\operatorname{Aut}(F)$; hence
$\operatorname{Aut}(F)$ is closed. If all $F(X)$ are finite the product
is profinite, and closed subgroups of profinite groups are profinite.
