+++
id = "lem-sf-tor-sheaf-constructible"
kind = "lemma"
title = "Tor sheaves of constructible sheaves"
order = 2118
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-derived-tensor", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, $n\geq1$, and
put $A=A_{E,n}$. Let $T$ be a scheme on which $\ell$ is invertible and
let $F$ and $G$ be
constructible sheaves
of $A_T$-modules on $T_{\mathrm{proet}}$. Then for every
$r\in\mathbf Z$ the
cohomology sheaf
$\mathcal H^r(F\otimes_A^LG)$ is constructible, and its stalk at a
geometric point $\bar t\to T$ is the finite $A$-module
$\operatorname{Tor}^A_{-r}(F_{\bar t},G_{\bar t})$.

## Proof

By [def-weil-finite-torsion-constructibility] there is a finite
partition $T=\bigsqcup_{\nu=1}^NT_\nu$ into locally closed constructible
subschemes such that both $F|_{T_\nu}$ and $G|_{T_\nu}$ are locally
constant with finite $A$-module stalks. Fix $\nu$, write $U=T_\nu$,
and let $\{U_\alpha\to U\}$ be a covering on which both restrictions
become constant, with finite $A$-module values $M_\alpha$ and
$N_\alpha$. Restriction to $U_\alpha$ is an exact functor commuting
with cohomology sheaves and with the derived tensor product of
[def-weil-derived-tensor], so

$$
\mathcal H^r\bigl(F\otimes_A^LG\bigr)\big|_{U_\alpha}
\cong\mathcal H^r\bigl(M_\alpha\otimes_A^LN_\alpha\bigr),
$$

the right-hand side being the constant sheaf with value
$\operatorname{Tor}^A_{-r}(M_\alpha,N_\alpha)$: compute
$M_\alpha\otimes_A^LN_\alpha$ with a free resolution of $M_\alpha$,
which is a K-flat complex of constant sheaves with constant cohomology.
The modules $\operatorname{Tor}^A_{-r}(M_\alpha,N_\alpha)$ are finite
because $A$ is Noetherian and $M_\alpha$, $N_\alpha$ are finite.
Hence $\mathcal H^r(F\otimes_A^LG)|_U$ is locally constant with finite
$A$-module stalks, and the finite partition $\{T_\nu\}$ exhibits
$\mathcal H^r(F\otimes_A^LG)$ as constructible in the sense of
[def-weil-finite-torsion-constructibility]. A geometric stalk is an
exact functor commuting with tensor products, which gives the stated
description of the stalks.
