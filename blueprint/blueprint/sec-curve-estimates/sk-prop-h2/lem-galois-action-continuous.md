+++
id = "lem-galois-action-continuous"
kind = "lemma"
title = "Continuity of the action of $\\operatorname{Aut}(F)$"
order = 968
uses = ["def-galois-category"]
+++
Let $\mathcal C$ be a category and $F:\mathcal C\to\mathbf{Sets}$ a
functor with all $F(X)$ finite, and let
$\operatorname{Aut}(F)\subseteq\prod_X\operatorname{Aut}(F(X))$ carry
the topology induced from the product of the discrete topologies, as in
[def-galois-category]. Then for every object $X$ the action map

$$
\operatorname{Aut}(F)\times F(X)\longrightarrow F(X),\qquad
(\gamma,x)\longmapsto\gamma_X(x),
$$

is continuous for the discrete topology on $F(X)$.

## Proof

By [def-galois-category] the topology on $\operatorname{Aut}(F)$
is the initial topology of the evaluation maps
$\gamma\mapsto\gamma_Y$ into the discrete finite groups
$\operatorname{Aut}(F(Y))$. Hence the map
$\operatorname{Aut}(F)\times F(X)\to\operatorname{Aut}(F(X))\times F(X)$,
$(\gamma,x)\mapsto(\gamma_X,x)$, is continuous, and so is the
evaluation map
$\operatorname{Aut}(F(X))\times F(X)\to F(X)$, both factors
$\operatorname{Aut}(F(X))$ and $F(X)$ being finite and discrete; the
action map is the composite of these two.
