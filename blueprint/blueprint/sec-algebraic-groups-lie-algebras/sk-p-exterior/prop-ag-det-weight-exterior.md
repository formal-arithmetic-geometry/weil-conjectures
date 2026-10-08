+++
id = "prop-ag-det-weight-exterior"
kind = "theorem"
title = "Determinant weights of an exterior power (conditional)"
order = 2561
uses = ["cor-mg-central-determinant-weight", "d-weights", "def-mg-weil-composition-series", "def-mg-weil-semisimplification", "def-wf-monodromy-data", "def-wf-weil-category", "lem-mg-common-positive-central-element", "lem-mg-composition-series-exists", "lem-mg-degree-component-functoriality", "lem-mg-filtered-exterior-power", "lem-mg-filtration-refinement", "lem-wf-schur-scalar"]
lean = ["Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, put
$|k_0|=q$, fix a real weight character $\lambda$ as in [d-weights], and let
$\mathcal F_0$ be a nonzero lisse
Weil sheaf on $X_0$. Choose a
composition series in the sense of
[def-mg-weil-composition-series], with simple factors
$A_1,\ldots,A_t$. Write $d_a=\dim A_a$ and let
$\gamma_a=\dw_\lambda(A_a)$.
Let $R$ be the set of distinct values among the $\gamma_a$, and put

$$
r(\gamma):=\sum_{\gamma_a=\gamma}d_a,
$$

Thus $\dim V=\sum_{\gamma\in R}r(\gamma)$. Let
$0\le r\le\dim V$, and assume that every $A_a$ and every
Jordan–Holder constituent of $\bigwedge^r\mathcal F_0$ has finite
geometric determinant. Then every Jordan–Holder constituent of
$\bigwedge^r\mathcal F_0$ has
determinant weight

$$
\sum_{\gamma\in R}n_\gamma\gamma,
\qquad 0\le n_\gamma\le r(\gamma),
\qquad \sum_{\gamma\in R}n_\gamma=r.
$$

Conversely every admissible tuple $(n_\gamma)$ occurs as the
determinant weight of at least one
Jordan–Holder constituent. The input factors
$\gamma_a$ are counted with multiplicity; the assertion concerns the
possible weights and their non-emptiness, not an equality of output
multiplicities for coincident sums.

## Proof

Write $V$ for the Weil representation. The factors and their weights
are those of
[def-mg-weil-composition-series] and [d-weights]. The Weil
semisimplification $V^{\mathrm{ss}}=\bigoplus_aA_a$ of
[def-mg-weil-semisimplification] is a semisimple Weil representation,
so [lem-mg-common-positive-central-element] applies to it, giving
a central element $z$ of degree $d>0$ (in the monodromy data of
[def-wf-monodromy-data]). For each simple
factor $A_a$, its image is
central by [lem-mg-degree-component-functoriality]. Its matrix
commutes with the Weil-group image on $A_a$, so
[lem-wf-schur-scalar] applies to this Weil-simple representation and
gives a scalar $c_a$. The central-element formula
[cor-mg-central-determinant-weight], applicable because $A_a$ has
finite geometric determinant, gives

$$
\gamma_a=\frac{\lambda(c_a)}{d}.
$$

By [lem-mg-filtered-exterior-power], $\bigwedge^rV$ has a finite
Weil-stable filtration with nonzero successive quotients

$$
Q_{\boldsymbol n}=\bigotimes_{a=1}^t\bigwedge^{n_a}A_a,
\qquad 0\le n_a\le d_a,
\qquad \sum_a n_a=r,
$$

each a tensor construction on subquotients of $V^{\mathrm{ss}}$.
The refinement lemma [lem-mg-filtration-refinement] reduces all
composition factors to these quotients. On $Q_{\boldsymbol n}$, the
central element acts by $c_{\boldsymbol n}:=\prod_a c_a^{n_a}$. Every
simple factor $C$ of this quotient receives a central degree-$d$ element
by [lem-mg-degree-component-functoriality]; its matrix commutes with
the Weil-group image on $C$, and therefore is scalar by Schur's lemma.
Since $C$ has finite geometric determinant by assumption,
[cor-mg-central-determinant-weight] gives

$$
\dw_\lambda(C)=\frac{\lambda(c_{\boldsymbol n})}{d}
=\sum_a n_a\gamma_a.
$$

Grouping equal $\gamma_a$'s gives the asserted aggregate tuple and its
capacity bounds. Conversely, for an admissible tuple $(n_\gamma)$,
distribute each $n_\gamma$ among the indices with $\gamma_a=\gamma$,
never exceeding $d_a$. The resulting $Q_{\boldsymbol n}$ is nonzero,
so [lem-mg-composition-series-exists] gives a simple factor, whose
weight is the required sum. This proves the converse.
