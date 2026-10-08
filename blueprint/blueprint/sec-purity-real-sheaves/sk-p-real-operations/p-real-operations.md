+++
id = "p-real-operations"
kind = "theorem"
title = "Local Frobenius polynomials"
order = 2592
uses = ["def-real-weil-representation-operations", "def-weil-local-frobenius-trace", "def-wf-fundamental-representation", "def-wf-iota-real", "def-wf-weil-group", "lem-wf-weil-group-constant-extension", "prop-wf-weil-sheaf-representation-equivalence"]
tags = ["latex:proposition"]
+++
Keep the notation of [prop-wf-weil-sheaf-representation-equivalence], so
that $(V,\rho)$ is the Weil fundamental representation of
[def-wf-fundamental-representation], and let $x$ be a closed point of
$C_0$ of degree $e_x$, with local Frobenius $F_x$ of
[def-weil-local-frobenius-trace] acting on the stalk
$\mathcal F_{\bar x}$; it acts through the conjugacy class of
geometric Frobenius elements at $x$ (images of the geometric Frobenius of
$k(x)$ under a decomposition-group map $\pi_1(x)\to\pi_1(C_0)$), of degree $e_x$, in the Weil group $W(C_0)$ of [def-wf-weil-group],
the geometric Frobenius over $k(x)$ having degree $e_x$ by
[lem-wf-weil-group-constant-extension]. (Changing the decomposition-group
map conjugates $F_x$ by some $g\in\pi_1(C_0)$, and this is a conjugation
inside $W(C_0)$: as $\widehat{\mathbf Z}=\mathbf Z+e_x\widehat{\mathbf Z}$,
one can write $g=wF_x^t$ with $w\in W(C_0)$ and $t\in\widehat{\mathbf Z}$,
where $F_x^t$ is the image of the $t$-th power of the geometric Frobenius
in the procyclic group $\pi_1(x)$, which commutes with $F_x$; so
$gF_xg^{-1}=wF_xw^{-1}$.) Use the tensor equivalence
[prop-wf-weil-sheaf-representation-equivalence] for the operations of
[def-real-weil-representation-operations] (direct sum, tensor product, dual,
exterior powers, determinant), and
write $P_x(\mathcal F,T)=\det(1-TF_x\mid\mathcal F_{\bar x})$ for the local
characteristic factor of [def-wf-iota-real]. Then

$$
P_x(\mathcal F,T)=\det\bigl(1-T\,\rho(F_x)\mid V\bigr)
\qquad\text{for every closed }x .
$$

## Proof

Granted [prop-wf-weil-sheaf-representation-equivalence], the operations of
[def-real-weil-representation-operations] on
lisse Weil sheaves are *defined* by transport along the equivalence, so
only the local polynomial needs an argument. Iterating the Frobenius
structure map $e_x$ times on the stalk at $\bar x$, as in
[def-weil-local-frobenius-trace], realizes $F_x$ as $\rho$ of
any member of the degree-$e_x$ class supplied by $x$. A characteristic
polynomial is invariant under conjugation, so $\det(1-T\rho(F_x)\mid V)$ is
independent of the member chosen and agrees with the stalkwise $P_x$ of [def-wf-iota-real].

Uses: [def-real-weil-representation-operations], [def-weil-local-frobenius-trace], [def-wf-fundamental-representation], [def-wf-iota-real], [def-wf-weil-group], [lem-wf-weil-group-constant-extension], [prop-wf-weil-sheaf-representation-equivalence]
