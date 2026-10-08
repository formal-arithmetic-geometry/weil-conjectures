+++
id = "cor-mg-det-weight-finite-tensor"
kind = "theorem"
title = "Determinant weights of a finite tensor power"
order = 2638
tags = ["latex:corollary"]
uses = ["def-mg-determinantal-weight-multiset", "def-mg-weil-composition-series", "def-real-weil-representation-operations", "def-wf-determinantal-weight", "def-wf-geometric-semisimplicity", "lem-mg-jordan-holder", "lem-rp-determinant-weights-agree", "prop-ag-det-weight-two-factor-tensor"]
+++
Let $\mathcal F_0$ be a nonzero lisse Weil sheaf with
semisimple geometric
representation on a normal geometrically connected curve $X_0$, and let
$\alpha_1,\ldots,\alpha_n$ be its determinant weights, counted with
multiplicity in [def-mg-determinantal-weight-multiset]. For every
$k\ge1$, every Jordan–Holder constituent of the tensor power
$\mathcal F_0^{\otimes k}$ (constituents and tensor products of Weil
representations as in [def-real-weil-representation-operations]) has
determinant weight

$$
\alpha_{i_1}+\cdots+\alpha_{i_k}
$$

for some indices $i_1,\ldots,i_k$, and every such sum occurs for at
least one constituent. In particular, if $\beta=\max_i\alpha_i$, the
largest determinant weight of $\mathcal F_0^{\otimes k}$ is
$k\beta$.

## Proof

Choose a composition series of the Weil representation in the sense of
[def-mg-weil-composition-series], with simple factors $A_i$. By
[lem-mg-jordan-holder] and [def-mg-determinantal-weight-multiset], after
reindexing, $\alpha_i=\dw_\iota(A_i)$ (the geometric semisimplicity of
[def-wf-geometric-semisimplicity] is not needed for the argument). By
[lem-rp-determinant-weights-agree], every $A_i$ and every
Jordan–Holder constituent of $\mathcal F_0^{\otimes k}$ has finite
geometric determinant, and for each of them the determinant weight
$\dw_\iota$ of [def-wf-determinantal-weight] equals
$\dw_{\lambda_\iota}$. We prove both assertions by induction on $k$,
using the two-factor tensor rule [prop-ag-det-weight-two-factor-tensor]
with $\lambda=\lambda_\iota$. For $k=1$ the constituents of
$\mathcal F_0$ are the $A_i$ by [lem-mg-jordan-holder], with
determinant weights $\alpha_i$. For $k\ge2$ apply
[prop-ag-det-weight-two-factor-tensor] to $\mathcal V_0=\mathcal
F_0^{\otimes(k-1)}$ and $\mathcal E_0=\mathcal F_0$, both nonzero and
lisse on $X_0$, with composition series whose factors are the
constituents of $\mathcal F_0^{\otimes(k-1)}$, respectively the $A_j$;
all of these, and all constituents of $\mathcal F_0^{\otimes k}$, have
finite geometric determinant by the previous paragraph. Every
constituent $Q$ of $\mathcal F_0^{\otimes k}$ therefore has
$\dw(Q)=\dw(V_i)+\alpha_j$ for a constituent $V_i$ of
$\mathcal F_0^{\otimes(k-1)}$, which by induction has weight
$\alpha_{i_1}+\cdots+\alpha_{i_{k-1}}$. Conversely, by induction every
sum $\alpha_{i_1}+\cdots+\alpha_{i_{k-1}}$ is the weight of some
constituent $V_i$, and the converse half of
[prop-ag-det-weight-two-factor-tensor] gives a constituent of
$\mathcal F_0^{\otimes k}$ of weight $\dw(V_i)+\alpha_{i_k}$. The
statement about $\beta$ follows by taking all indices with
$\alpha_{i_r}=\beta$.
