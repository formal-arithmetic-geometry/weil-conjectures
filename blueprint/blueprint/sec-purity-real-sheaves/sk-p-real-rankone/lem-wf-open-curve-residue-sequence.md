+++
id = "lem-wf-open-curve-residue-sequence"
kind = "lemma"
title = "Finite-level residue sequences on an open curve"
order = 2624
uses = ["def-coefficient-twists-detailed", "def-tw-frobenius-action", "def-weil-frobenius-coefficient-twists", "lem-pur-support-localization-triangle", "lem-sc-point-cartier", "prop-pur-regular-immersion-purity-compatibilities", "thm-pur-regular-immersion-purity"]
+++
Let $C_0/\mathbf F_q$ be a smooth projective geometrically connected
curve, let $D_0\subset C_0$ be a finite reduced closed subscheme, and put
$U_0=C_0-D_0$. After base change to
$\overline{\mathbf F}_q$, write $j:U\hookrightarrow C$ and
$i:D\hookrightarrow C$. Put $A_n=\mathbf Z/\ell^n\mathbf Z$, with
$\ell\ne\operatorname{char}\mathbf F_q$. For every $n\geq1$, there is
a Frobenius-equivariant exact sequence

$$
0\longrightarrow H^1(C,A_n)\xrightarrow{j^*}H^1(U,A_n)
\xrightarrow{\operatorname{res}_n}H^0(D,A_n(-1))
\longrightarrow H^2(C,A_n).
\tag{5.1}
$$

The sequences and their transition maps in $n$ are compatible. There
is $m\geq1$ such that, for $Q=q^m$, $\Phi_Q$ fixes every geometric
point of $D$; on the inverse-limit boundary module

$$
\varprojlim_n H^0(D,A_n(-1))
$$

it acts as multiplication by $Q$, and this module has no
$\Phi_Q$-fixed element. Frobenius and twists are those of
[def-tw-frobenius-action], [def-coefficient-twists-detailed].

## Proof

The geometric boundary $D$ is a finite disjoint union of closed points of
the smooth curve $C$. Each point is an effective Cartier divisor by
[lem-sc-point-cartier]; hence $i$ is a regular closed immersion of
pure codimension one. For every $n$, purity in
[thm-pur-regular-immersion-purity] gives

$$
Ri^!A_{n,C}\xrightarrow{\sim}A_{n,D}(-1)[-2].
\tag{5.2}
$$

The finite-reduction compatibility in
[prop-pur-regular-immersion-purity-compatibilities] makes (5.2)
compatible with $n$. Apply the support-localization triangle
[lem-pur-support-localization-triangle] at level $n$:

$$
R\Gamma(D,Ri^!A_{n,C})\longrightarrow R\Gamma(C,A_n)
\longrightarrow R\Gamma(U,A_n)\xrightarrow{+1}.
\tag{5.3}
$$

The shift in (5.2) gives $H_D^1(C,A_n)=0$ and
$H_D^2(C,A_n)=H^0(D,A_n(-1))$. The degree-one part of the long exact
sequence of (5.3) is (5.1). Naturality of purity and localization gives
Frobenius equivariance and compatibility under reduction.

Frobenius permutes the finite set $D(\overline{\mathbf F}_q)$. Choose
$m$ divisible by all cycle lengths. Then $\Phi_Q=\Phi_q^m$ fixes every
point. By the normalization in
[def-weil-frobenius-coefficient-twists], it acts on
$A_n(-1)$ by $Q\bmod\ell^n$. Hence it acts on the inverse limit as
the scalar $Q$ on the finite free $\mathbf Z_\ell$-module
$\mathbf Z_\ell(-1)^{D(\overline{\mathbf F}_q)}$. Since $Q-1\ne0$ and
this module is torsion-free, its fixed element is zero.
