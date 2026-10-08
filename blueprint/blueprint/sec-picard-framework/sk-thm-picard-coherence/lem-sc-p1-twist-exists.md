+++
id = "lem-sc-p1-twist-exists"
kind = "lemma"
title = "The twists $\\mathcal O(d)$ exist"
order = 636
uses = ["def-sc-invertible-module", "def-sc-p1-standard"]
+++
Let $k$ be a field, $d\in\mathbf Z$, and let
$U_0,U_1,U_{01}$ be the standard affine cover of
$\mathbf P^1_k$ of [def-sc-p1-standard]. Then a twisted
structure sheaf $\mathcal O(d)$ as in
[def-sc-p1-standard] exists, and it is an
invertible
$\mathcal O_{\mathbf P^1_k}$-module; it is unique up to unique
isomorphism compatible with the generating sections $g_0,g_1$.

## Proof

Over $U_0$ take the free rank-one module
$\mathcal O_{U_0}\cdot g_0$, over $U_1$ the free rank-one module
$\mathcal O_{U_1}\cdot g_1$, and over $U_{01}$ the isomorphism
$g_0\mapsto t^{-d}g_1$ of [def-sc-p1-standard]; it is an
isomorphism because $t^{-d}\in k[t,t^{-1}]=\Gamma(U_{01},\mathcal O_{\mathbf P^1_k})$ is a unit. The cover
$\mathbf P^1_k=U_0\cup U_1$ has two members, so $U_{01}$ is the
only nonempty multiple overlap and the cocycle condition for
glueing is the single relation $t^{d}\cdot t^{-d}=1$ there, which
holds. Hence the local free modules glue to a sheaf
$\mathcal O(d)$ of $\mathcal O_{\mathbf P^1_k}$-modules, unique
up to unique isomorphism compatible with $g_0$ and $g_1$, and
$\mathcal O(d)$ is free of rank one over each of $U_0$ and
$U_1$, i.e. invertible ([def-sc-invertible-module]).
