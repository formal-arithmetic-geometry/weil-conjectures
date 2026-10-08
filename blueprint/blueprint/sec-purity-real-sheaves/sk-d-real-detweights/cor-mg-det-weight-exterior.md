+++
id = "cor-mg-det-weight-exterior"
kind = "theorem"
title = "Determinant weights of an exterior power"
order = 2639
tags = ["latex:corollary"]
uses = ["def-mg-determinantal-weight-multiset", "def-mg-weil-composition-series", "def-real-weil-representation-operations", "def-wf-determinantal-weight", "def-wf-geometric-semisimplicity", "lem-rp-determinant-weights-agree", "prop-ag-det-weight-exterior"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, put
$|k_0|=q$, fix $\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let
$\mathcal F_0$ be a nonzero lisse
Weil sheaf on $X_0$ with
semisimple geometric
representation. Choose a
composition series in the sense of
[def-mg-weil-composition-series], with simple factors
$A_1,\ldots,A_t$. Write $d_a=\dim A_a$ and let $\gamma_a$ be the
determinantal weight of $A_a$.
Let $R$ be the set of distinct values among the $\gamma_a$, and put

$$
r(\gamma):=\sum_{\gamma_a=\gamma}d_a,
$$

Thus $\dim V=\sum_{\gamma\in R}r(\gamma)$. For every
$0\le r\le\dim V$, every Jordan–Holder constituent of the exterior
power $\bigwedge^r\mathcal F_0$ (constituents and exterior powers of
Weil representations as in [def-real-weil-representation-operations])
has determinant weight

$$
\sum_{\gamma\in R}n_\gamma\gamma,
\qquad 0\le n_\gamma\le r(\gamma),
\qquad \sum_{\gamma\in R}n_\gamma=r.
$$

Conversely every admissible tuple $(n_\gamma)$ occurs as the
determinant weight of at least one
Jordan–Holder constituent. The input factors
$\gamma_a$ are counted with multiplicity as in
[def-mg-determinantal-weight-multiset]; the assertion concerns the
possible weights and their non-emptiness, not an equality of output
multiplicities for coincident sums.

## Proof

The factors $A_a$ are those of the chosen series of
[def-mg-weil-composition-series], counted as in
[def-mg-determinantal-weight-multiset], and $\gamma_a$ is their
determinantal weight in the sense of [def-wf-determinantal-weight] (the
geometric semisimplicity of [def-wf-geometric-semisimplicity] is not
needed for the argument). By [lem-rp-determinant-weights-agree], every
$A_a$ and every Jordan–Holder constituent of
$\bigwedge^r\mathcal F_0$ has finite geometric determinant, and for
each of them $\dw_\iota$ equals $\dw_{\lambda_\iota}$. Hence
[prop-ag-det-weight-exterior], applied with $\lambda=\lambda_\iota$, gives the assertion and
its converse.
