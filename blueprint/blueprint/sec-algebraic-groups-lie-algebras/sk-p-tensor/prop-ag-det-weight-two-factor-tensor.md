+++
id = "prop-ag-det-weight-two-factor-tensor"
kind = "theorem"
title = "Determinant weights of a tensor product of two sheaves (conditional)"
order = 2559
uses = ["cor-mg-central-determinant-weight", "d-weights", "def-mg-weil-composition-series", "def-mg-weil-semisimplification", "lem-mg-common-positive-central-element", "lem-mg-composition-series-exists", "lem-mg-degree-component-functoriality", "lem-mg-filtered-tensor-product", "lem-mg-filtration-refinement", "lem-mg-jordan-holder", "lem-wf-schur-scalar"]
lean = ["Representation.exists_detWeight_eq_add_of_subquotient_tprod"]
+++
Fix a real weight character $\lambda$ as in [d-weights]. Let
$\mathcal V_0$ and $\mathcal E_0$ be nonzero lisse Weil sheaves on the
same normal geometrically connected curve $X_0$, with Weil
representations $V$ and $E$. Choose composition series in the sense of
[def-mg-weil-composition-series], with simple factors
$V_1,\ldots,V_t$ of $V$ and $E_1,\ldots,E_u$ of $E$. Assume that every
$V_i$, every $E_j$, and every Jordan–Holder constituent of
$V\otimes E$ has finite geometric determinant. Then for every
Jordan–Holder constituent $Q$ of $V\otimes E$ there is a pair $(i,j)$
with

$$
\dw_\lambda(Q)=\dw_\lambda(V_i)+\dw_\lambda(E_j).
$$

Conversely, every such sum occurs for at least one constituent. Neither
$V$, $E$ nor $V\otimes E$ is assumed semisimple.

## Proof

The multisets $\{V_i\}$ and $\{E_j\}$ do not depend on the chosen
series by [lem-mg-jordan-holder]. Form the Weil semisimplifications
$V^{\mathrm{ss}}=\bigoplus_iV_i$ and $E^{\mathrm{ss}}=\bigoplus_jE_j$
of [def-mg-weil-semisimplification]; both are semisimple Weil
representations on the same curve. Apply
[lem-mg-common-positive-central-element] to the pair
$V^{\mathrm{ss}},E^{\mathrm{ss}}$, i.e. to
$\rho=V^{\mathrm{ss}}\oplus E^{\mathrm{ss}}$, and let $z$ be the
resulting central element of degree $m>0$. Each $V_i$ and each $E_j$
is a Weil-stable direct summand, hence a subquotient, of $\rho$, so by
[lem-mg-degree-component-functoriality] the image of $z$ on it is
central of degree $m$; by [lem-wf-schur-scalar] it acts on $V_i$ by a
scalar $c_i$ and on $E_j$ by a scalar $d_j$. Since $V_i$ and $E_j$
have finite geometric determinant, [cor-mg-central-determinant-weight]
gives

$$
\dw_\lambda(V_i)=\frac{\lambda(c_i)}{m},\qquad
\dw_\lambda(E_j)=\frac{\lambda(d_j)}{m}.
$$

By [lem-mg-filtered-tensor-product], $V\otimes E$ has a Weil-stable
filtration whose successive quotients are the representations
$V_i\otimes E_j$, each pair $(i,j)$ occurring once. Each
$V_i\otimes E_j$ is a tensor product of two subquotients of $\rho$, so
[lem-mg-degree-component-functoriality] applies to it and to its
iterated subquotients, and the image of $z$ acts on $V_i\otimes E_j$
by $c_id_j$. By [lem-mg-filtration-refinement], every constituent $Q$
of $V\otimes E$ is a composition factor of some $V_i\otimes E_j$. The
image of $z$ on $Q$ is central of degree $m$ by the same
functoriality, acts by the scalar $c_id_j$, and $Q$ has finite
geometric determinant by hypothesis; therefore
[cor-mg-central-determinant-weight] and the fact that $\lambda$ is a
homomorphism give

$$
\dw_\lambda(Q)=\frac{\lambda(c_id_j)}{m}
=\frac{\lambda(c_i)}{m}+\frac{\lambda(d_j)}{m}
=\dw_\lambda(V_i)+\dw_\lambda(E_j).
$$

Conversely, each $V_i\otimes E_j$ is nonzero, so it has a composition
series by [lem-mg-composition-series-exists]; its factors are
constituents of $V\otimes E$ by [lem-mg-filtration-refinement], and
each has determinant weight $\dw_\lambda(V_i)+\dw_\lambda(E_j)$.
