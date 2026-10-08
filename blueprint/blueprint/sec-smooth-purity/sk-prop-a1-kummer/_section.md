+++
id = "sk-prop-a1-kummer"
kind = "section"
title = "The affine line and $\\mathbf G_m$ with $\\Lambda(1)$-coefficients"
order = 1900
uses = ["sk-def-av-pic", "sk-def-curve", "sk-def-purity-conv", "sk-prop-cd", "sk-prop-cd-affine", "sk-prop-kummer-exact", "sk-thm-smooth-base-change"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine", "AlgebraicGeometry.Etale.nonempty_iso_homology_zero_multiplicativeGroup", "AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup", "AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup"]
+++
*Proposition (sketch).*

In the conventions of [sk-def-purity-conv], write
$p:\Aaf^1_Y\to Y$ for the projection, $j:\mathbf G_{m,Y}\hookrightarrow \Aaf^1_Y$ for the open complement of the zero section, and $\pi=pj$.
For every separated finite-type $Y$:

- **(a)** *Acyclicity of the affine line.*
$Rp_*\Lambda\simeq\Lambda_Y$; equivalently $R^mp_*\Lambda=0$ for $m>0$.
- **(b)** *The Kummer generator.* $R^0\pi_*\Lambda(1)\simeq\Lambda_Y(1)$,
with $p^*$ an isomorphism onto it, and $R^1\pi_*\Lambda(1)\simeq\Lambda_Y$
is free of rank one on the Kummer class $\kappa(t)$.
- **(c)** *Vanishing above degree one.* $R^m\pi_*\Lambda(1)=0$ for $m\ge2$.

All three are compatible with base change on $Y$, as is $\kappa(t)$.
Equivalently, (a)–(c) are the corresponding statements for
$\Aaf^1$ and $\mathbf G_m$ over a geometric point.
Compare Milne, *Lectures on Étale Cohomology*, §16; SGA 4, IX.

## Proof

*Reduction to a geometric fibre.* Smoothness of $p$ and $\pi$ is
*not* what reduces the statement to a fibre: smooth base change
([sk-thm-smooth-base-change]) requires the *base-changing* arrow to
be smooth, and the formation of a direct image does not in general commute
with an arbitrary base change of $Y$ (for $j:\mathbf G_{m,k}\hookrightarrow \Aaf^1_k$ one has $(j_*\Lambda)_{\bar 0}=\Lambda$, while the source
base-changed to $\bar 0$ is empty). The reduction is the following, with
$k=\overline{\mathbf F}_q$ the algebraically closed field of
[sk-def-sf-setting] over which $Y$ lives. Let $\bar y$ be a geometric
point of $Y$ and $S'=\Spec\mathcal O^{\mathrm{sh}}_{Y,\bar y}$ its strict
henselization, a $k$-scheme. As $p$ and $\pi$ are quasi-compact and
quasi-separated, the stalk formula gives
$(Rp_*\Lambda)_{\bar y}\simeq R\Gamma(\Aaf^1_{S'},\Lambda)$ and
$(R\pi_*\Lambda(1))_{\bar y}\simeq R\Gamma(\mathbf G_{m,S'},\Lambda(1))$,
compatibly with $p^*$ and with the restriction of $\kappa(t)$. Now
$\Aaf^1_{S'}=\Aaf^1_k\times_kS'$, and smooth base change applies to the
Cartesian square whose *smooth* side is $\Aaf^1_k\to\Spec k$ and whose
base-changing arrow is $g:S'\to\Spec k$ (quasi-compact quasi-separated), for
the constant sheaf $\Lambda$ on $S'$: with $h:\Aaf^1_{S'}\to\Aaf^1_k$ the
projection, $f^{-1}R^qg_*\Lambda\xrightarrow{\sim}R^qh_*\Lambda$. Since $S'$
is strictly henselian and $k$ algebraically closed, $R^qg_*\Lambda$ is the
constant sheaf $H^q(S',\Lambda)$, i.e. $\Lambda$ for $q=0$ and $0$ for
$q>0$; hence $\Lambda_{\Aaf^1_k}\xrightarrow{\sim}Rh_*\Lambda$ and
$h^*:R\Gamma(\Aaf^1_k,\Lambda)\xrightarrow{\sim}R\Gamma(\Aaf^1_{S'},\Lambda)$.
The same square with $\mathbf G_{m,k}$ in place of $\Aaf^1_k$ gives
$h^*:R\Gamma(\mathbf G_{m,k},\Lambda(1))\xrightarrow{\sim} R\Gamma(\mathbf G_{m,S'},\Lambda(1))$, carrying the Kummer class of the
coordinate of $\mathbf G_{m,k}$ to the restriction of $\kappa(t)$ (the Kummer
boundary commutes with pullback). These are the specific
$\Aaf^1$- and $\mathbf G_m$-homotopy-invariance inputs over a strictly
henselian base (§[sec-smooth-base-change] does not use the present
section, so the reference is not circular). All three clauses are
statements about cohomology sheaves and about the sections $p^*$, $\kappa(t)$
of them, so they may be checked on geometric stalks, where they become the
corresponding statements for $\Aaf^1_k$ and $\mathbf G_{m,k}$ over the
algebraically closed $k$; geometric stalks are conservative. Then
$\Aaf^1_k$ and $\mathbf G_{m,k}$ are affine curves in the sense of
[sk-def-curve]. The twist $\Lambda(1)$ is pulled back from $Y$, so by the
projection formula the twisted and untwisted statements determine one
another.

*Base change on $Y$.* For $g:Y'\to Y$ with base changes $p',\pi'$ and
coordinate $t'$, the base-change maps $g^*Rp_*\Lambda\to Rp'_*\Lambda$ and
$g^*R\pi_*\Lambda(1)\to R\pi'_*\Lambda(1)$ are compatible with the units
$p^*,\pi^*$ and carry $g^*\kappa(t)$ to $\kappa(t')$. Once (a)–(c) are
known over $Y$ and over $Y'$, both sides have cohomology sheaves only in
degree $0$ (resp. degrees $0,1$), identified by these sections, so the
base-change maps are isomorphisms. The compatibility with base change in
the statement is thus a consequence of (a)–(c), not an input to their proof.

*Coefficients.* With $N$ as in [sk-def-purity-conv], $\ell^NA=0$ and
$\Lambda(1)=\mu_{\ell^N}\otimes_{\Z/\ell^N\Z}A$. We reduce to
$\mu_{\ell^N}$-coefficients by dévissage on $n$. For $n=1$,
$A=F=\mathcal O_E/\varpi$ is a finite-dimensional $\mathbf F_\ell$-vector
space, so $F(1)=\mu_\ell\otimes_{\mathbf F_\ell}F$ is a finite direct sum of
copies of $\mu_\ell$ and (a)–(c) for $F$ follow from the computation below
(with $\ell^N=\ell$). For $n>1$ the exact sequence
$0\to A_{E,n-1}\xrightarrow{\varpi}A_{E,n}\to F\to0$ of coefficient modules
gives an exact sequence of twisted sheaves; the vanishings in (a) and (c)
pass through the long exact sequence, and for (b), on $C=\mathbf G_{m,k}$,
the connecting map $H^0(C,F(1))\to H^1(C,A_{E,n-1}(1))$ vanishes because
$H^0(C,A_{E,n}(1))=\mu_{\ell^N}(k)\otimes A_{E,n}\to H^0(C,F(1))$ is
surjective ($k$ algebraically closed) and $H^2(C,A_{E,n-1}(1))=0$ by
induction; since $a\mapsto a\cdot\kappa(t)$ and $p^{*}$ are natural in the
coefficient module, the five lemma applied to
$0\to A_{E,n-1}\to A_{E,n}\to F\to0$ and
$0\to H^1(C,A_{E,n-1}(1))\to H^1(C,A_{E,n}(1))\to H^1(C,F(1))\to0$ (and to
the corresponding $H^0$-sequence) gives (b) for $A_{E,n}$. (When
$e(E/\mathbf Q_\ell)\mid n$ and $N=n/e$, $A\cong(\Z/\ell^N\Z)^{ef}$ is free
over $\Z/\ell^N\Z$, and one may instead tensor the $\mu_{\ell^N}$-computation
with $A$ directly.)

*Clause (c).* $\ell$ is prime to $\operatorname{char}k$ and both curves
are affine, so [sk-prop-cd-affine] gives $H^q(-,\mu_{\ell^N})=0$ for $q\ge2$.
This is (c), and it reduces (a) and (b) to degrees $0$ and $1$.

*Degrees $0$ and $1$.* By [sk-prop-kummer-exact] with $n=\ell^N$
invertible, the Kummer sequence gives

$$
0\to H^0(C,\mu_{\ell^N})\to\Gamma(C,\mathbb G_m)
\xrightarrow{\ \ell^N\ }\Gamma(C,\mathbb G_m)\to H^1(C,\mu_{\ell^N})\to\Pic(C).
$$

For $C=\Aaf^1_k$: $\Gamma(C,\mathbb G_m)=k^\times$ and $\Pic(C)=0$, since
$k[T]$ is a principal ideal domain. As $k$ is algebraically closed,
$k^\times$ is divisible, so the $\ell^N$-power map is surjective and
$H^1(\Aaf^1_k,\mu_{\ell^N})=0$. With (c) this gives $R^mp_*\Lambda=0$ for
$m>0$, and $R^0p_*\Lambda=\Lambda_Y$ because the geometric fibres $\Aaf^1_k$ are
connected; this is (a).
For $C=\mathbf G_{m,k}$: $\Gamma(C,\mathbb G_m)=k^\times\times t^{\Z}$, the
units of $k[T,T^{-1}]$, and $\Pic(C)=0$. Divisibility of $k^\times$ leaves
$\Gamma(C,\mathbb G_m)/\ell^N\cong t^{\Z}/\ell^Nt^{\Z}\cong\Z/\ell^N\Z$, so
$H^1(\mathbf G_{m,k},\mu_{\ell^N})$ is free of rank one on the class of $t$,
which is $\kappa(t)$ by [sk-def-purity-conv]; and
$H^0(\mathbf G_{m,k},\mu_{\ell^N})=\mu_{\ell^N}(k)$ is free of rank one, with
restriction from $\Aaf^1_k$ an isomorphism onto it. Tensoring with $F$
and the dévissage above give (b).

Uses: [sk-def-curve], [sk-def-purity-conv], [sk-prop-cd], [sk-prop-kummer-exact], [sk-thm-smooth-base-change]
