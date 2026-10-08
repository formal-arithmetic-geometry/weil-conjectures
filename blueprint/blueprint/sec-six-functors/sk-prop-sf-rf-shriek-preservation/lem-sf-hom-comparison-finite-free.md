+++
id = "lem-sf-hom-comparison-finite-free"
kind = "lemma"
title = "The internal-Hom comparison for a bounded free model"
order = 2083
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-constructible-complexes", "def-weil-pbc-site-comparison-morphism", "def-weil-site-perfect-complex", "lem-sf-hom-finite-projective"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$, $A=A_{E,n}$, and let $T$ be a scheme on which $\ell$ is
invertible. Let $P'$ be a bounded complex of finite free
$A_{T,\Et}$-modules, so that $P'$ is
site-perfect in the sense of
[def-weil-site-perfect-complex], and let $N$ be a bounded complex of
$A$-module sheaves with constructible cohomology on the small étale site
of $T$, in the sense of
[def-weil-pbc-constructible-complexes]. For the comparison morphism
$\nu_T:T_{\Proet}\to T_{\Et}$ of
[def-weil-pbc-site-comparison-morphism] the comparison map of
[def-weil-derived-pullback-tensor-hom],

$$
\nu_T^*R\mathcal H om_A(P',N)\longrightarrow
R\mathcal H om_A(\nu_T^*P',\nu_T^*N),
$$

is an isomorphism. The second variable is required only to be a bounded
complex with constructible cohomology: no étale finite-Tor hypothesis
on it is used.

## Proof

Write $P'^\vee=R\mathcal H om_A(P',A_T)$, so that
$P'^{\vee,i}=\mathcal H om_A(P'^i,A_T)$ is again finite free. For a
bounded complex $P'$ of finite free modules the termwise identity
$\mathcal H om_A(P'^i,N^j)\cong(P'^i)^\vee\otimes_AN^j$ of
[lem-sf-hom-finite-projective], with the total-complex signs, is a
computation of finite free modules and uses nothing about $N$ beyond its
being a complex of modules; it gives

$$
P'^\vee\otimes_A^LN\cong R\mathcal H om_A(P',N),
$$

the finite free modules being flat, so that the derived tensor product of
[def-weil-derived-tensor] is computed by the ordinary tensor complex.
The comparison pullback $\nu_T^*$ is exact, is monoidal and carries finite
free modules to finite free modules by
[def-weil-derived-pullback-tensor-hom]; hence
$\nu_T^*(P'^\vee)\cong(\nu_T^*P')^\vee$ termwise, and the same computation
on the pro-étale side, applied to the bounded complex $\nu_T^*P'$ of
finite free modules and to $\nu_T^*N$, gives

$$
R\mathcal H om_A(\nu_T^*P',\nu_T^*N)
\cong(\nu_T^*P')^\vee\otimes_A^L\nu_T^*N
\cong\nu_T^*\bigl(P'^\vee\otimes_A^LN\bigr)
\cong\nu_T^*R\mathcal H om_A(P',N).
$$

Both the comparison map and this composite are induced by the evaluation of
[lem-sf-hom-finite-projective] and its pullback, so they agree, and the
comparison is an isomorphism.
