+++
id = "lem-wf-additive-characters-h1"
kind = "lemma"
title = "Continuous $\\mathbf Z_\\ell$-characters are compatible finite-level classes"
order = 2619
uses = ["def-weil-pbc-etale-cohomology", "def-wf-weil-group", "lem-wf-finite-constant-h1-pi1"]
+++
Let $U_0/k_0$ be geometrically connected and separated of finite type,
put $U=U_0\times_{k_0}\overline{k}_0$, and choose a geometric point
$\bar u\to U$. Put $A_n=\mathbf Z/\ell^n\mathbf Z$. There is a
natural Frobenius-equivariant isomorphism

$$
\operatorname{Hom}_{\mathrm{cont}}(\pi_1(U,\bar u),\mathbf Z_\ell)
\xrightarrow{\sim}
\varprojlim_n H^1_{\mathrm{\acute et}}(U,A_n).
\tag{3.2}
$$

Under the Weil-group action determined by a
degree-one lift $s$, Frobenius on the left is

$$
f\longmapsto\bigl[g\longmapsto f(s^{-1}gs)\bigr].
$$

The cohomology and Weil-group conventions are those of
[def-weil-pbc-etale-cohomology], [def-wf-weil-group].

## Proof

At level $n$, [lem-wf-finite-constant-h1-pi1] gives

$$
H^1(U,A_n)\cong
\operatorname{Hom}_{\mathrm{cont}}(\pi_1(U,\bar u),A_n).
\tag{3.3}
$$

Its naturality shows that the transition map is reduction modulo
$\ell^n$. A compatible family on the right of (3.3) gives, point by
point, a homomorphism to
$\varprojlim_nA_n=\mathbf Z_\ell$. It is continuous because the inverse
image of $\ell^n\mathbf Z_\ell$ is the open kernel of its level-$n$
reduction. Conversely, reducing a continuous $\mathbf Z_\ell$-valued
homomorphism gives such a family. This proves (3.2). The explicit
Weil-descent computation in [lem-wf-finite-constant-h1-pi1], together
with [def-wf-weil-group], gives precomposition by
$g\mapsto s^{-1}gs$, which is the asserted Frobenius action.
