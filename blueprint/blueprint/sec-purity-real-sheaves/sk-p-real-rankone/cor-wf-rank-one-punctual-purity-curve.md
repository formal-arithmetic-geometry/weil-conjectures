+++
id = "cor-wf-rank-one-punctual-purity-curve"
kind = "theorem"
title = "Punctual purity of a rank-one Weil character on a curve"
order = 2628
tags = ["latex:corollary"]
uses = ["cor-wf-rank-one-degree-factorization-curve", "def-weil-local-frobenius-trace", "def-weil-punctual-weights", "def-wf-fundamental-representation", "def-wf-weil-group", "lem-tw-root-of-unity-modulus", "p-real-operations", "thm-wf-rank-one-finite-geometric-image-curve"]
+++
In the situation of
[thm-wf-rank-one-finite-geometric-image-curve], with $c$ and
$\varepsilon$ from [cor-wf-rank-one-degree-factorization-curve]
(applicable because $\chi(\Pi)$ is finite by that theorem), fix an embedding
$\iota:\overline{\mathbf Q}_\ell\hookrightarrow\mathbf C$, and use its
restriction to $E$ (equivalently, choose an embedding $E\hookrightarrow \mathbf C$ and an extension to $\overline{\mathbf Q}_\ell$). The rank-one lisse Weil sheaf
associated with $\chi$ by the
fundamental representation
is punctually $\iota$-pure of the
real weight

$$
w_\iota(\chi)=2\log_q|\iota(c)|,
$$

where $c=\chi(s)$ for any
degree-one element $s$.
The sheaf, degree, and punctual-purity conventions are those of
[def-wf-fundamental-representation], [def-wf-weil-group], [def-weil-punctual-weights].

## Proof

Let $x\in|U_0|$ be closed and set
$d=[\kappa(x):\mathbf F_q]$. The local geometric-Frobenius operator of
[def-weil-local-frobenius-trace] is represented in the Weil group by
a conjugacy class $F_x$ of degree $d$ [p-real-operations], with degree as in
[def-wf-weil-group]. Because $\chi$ is one-dimensional, its value
on this class is well defined. The factorization of
[cor-wf-rank-one-degree-factorization-curve] gives its unique stalk
eigenvalue as

$$
\alpha_x=\chi(F_x)=\varepsilon(F_x)c^d.
$$

The character $\varepsilon$ has finite image, so
$\varepsilon(F_x)$ is a root of unity. By
[lem-tw-root-of-unity-modulus],
$|\iota(\varepsilon(F_x))|=1$. Therefore

$$
|\iota(\alpha_x)|=|\iota(c)|^d
=q^{d w_\iota(\chi)/2}
=|\kappa(x)|^{w_\iota(\chi)/2}.
$$

This is precisely the definition in [def-weil-punctual-weights].
If $s'=gs$ is another degree-one lift, then
$\chi(s')/\chi(s)=\chi(g)$ is a root of unity by
[thm-wf-rank-one-finite-geometric-image-curve]; hence its complex
modulus is one and the displayed weight does not depend on $s$.
