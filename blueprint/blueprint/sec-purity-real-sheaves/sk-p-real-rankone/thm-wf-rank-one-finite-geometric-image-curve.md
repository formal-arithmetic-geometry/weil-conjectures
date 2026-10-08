+++
id = "thm-wf-rank-one-finite-geometric-image-curve"
kind = "theorem"
title = "Finite geometric image of a rank-one Weil character on a curve"
order = 2626
uses = ["def-weil-pbc-scheme-conventions", "def-wf-weil-group", "lem-wf-additive-characters-h1", "lem-wf-compact-character-logarithm", "lem-wf-deep-principal-unit-log", "prop-wf-open-curve-h1-no-frobenius-fixed"]
+++
Let $U_0/\mathbf F_q$ be normal, geometrically connected,
separated and of finite type,
pure of dimension one. Put
$U=U_0\times_{\mathbf F_q}\overline{\mathbf F}_q$ and
$\Pi=\pi_1(U,\bar u)$. Let $\ell\nmid q$, let
$E/\mathbf Q_\ell$ be finite, and let

$$
\chi:\hyperref[def-wf-weil-group]{W(U_0,\bar u)}\longrightarrow E^\times
$$

be a continuous character. Then $\chi(\Pi)$ is finite. Equivalently,
there is $N\geq1$ such that $\chi(g)^N=1$ for every $g\in\Pi$.
The scheme and Weil-group conventions are those of
[def-weil-pbc-scheme-conventions], [def-wf-weil-group].

## Proof

Choose $s\in W(U_0,\bar u)$ of degree one. By
[lem-wf-compact-character-logarithm], there are $N,r\geq1$ and a
continuous additive character

$$
\lambda(g)=\log(\chi(g)^N):\Pi\longrightarrow E
$$

which is invariant under $g\mapsto s^{-1}gs$. The Frobenius-equivariant
isomorphism of [lem-wf-additive-characters-h1] is applied after
choosing a $\mathbf Q_\ell$-basis $e_1,\ldots,e_d$ of $E$ and its
dual coordinate maps $t_i:E\to\mathbf Q_\ell$. Each
$f_i=t_i\circ\lambda$ is a continuous additive character invariant under
$g\mapsto s^{-1}gs$. Its image is compact, hence bounded; choose one
integer $a$ such that
$\ell^a f_i(\Pi)\subseteq\mathbf Z_\ell$ for every $i$. Put
$f_i'=\ell^a f_i$. The lemma gives compatible reductions

$$
[f'_{i,n}]\in H^1_{\mathrm{\acute et}}(U,\mathbf Z/\ell^n\mathbf Z)
\qquad(n\geq1).
\tag{6.1}
$$

Their Frobenius invariance follows from the invariance of $\lambda$ and
the equivariance in [lem-wf-additive-characters-h1]. Hence (6.1) is a
fixed element of the inverse limit, and it is zero by
[prop-wf-open-curve-h1-no-frobenius-fixed]. The isomorphism in
[lem-wf-additive-characters-h1] then gives $f_i'=0$, for every
$i$. Since the $t_i$ separate points of $E$, $\lambda=0$ on
$\Pi$.

The logarithm is injective on $1+\mathfrak m_E^r$ by
[lem-wf-deep-principal-unit-log]. It follows that

$$
\chi(g)^N=1\qquad(g\in\Pi).
$$

Thus $\chi(\Pi)$ is contained in the set of roots of the polynomial
$T^N-1$, and is finite. Conversely, if $\chi(\Pi)$ is finite, its
exponent supplies such an $N$.
