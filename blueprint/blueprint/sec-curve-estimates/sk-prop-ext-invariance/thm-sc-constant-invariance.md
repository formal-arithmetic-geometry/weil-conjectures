+++
id = "thm-sc-constant-invariance"
kind = "theorem"
title = "Base-change invariance for constant sheaves"
order = 1031
uses = ["def-sc-curves", "def-sc-field-extension", "def-sc-genus", "lem-sc-base-change-curve", "lem-sc-brauer-zero", "lem-sc-cohomological-dimension", "lem-sc-compactification", "lem-sc-genus-invariant", "lem-sc-kummer-les", "lem-sc-pic-affine", "lem-sc-pic-proper-ntorsion", "lem-sc-primitive-root", "thm-av-final", "thm-sc-jacobian-representability", "thm-sc-proper-cohomology"]
+++
Let $k\subseteq k'$ be algebraically closed, let $C$ be a
smooth separated connected curve over $k$, let
$\overline C$ be a compactification of $C$
([lem-sc-compactification]; thus $\overline C=C$ when $C$
is proper), and let
$g:=g(\overline C)$ ([def-sc-genus]). Let $n\geq1$ be
prime to $\operatorname{char}k$.
For every $q\geq0$, the pullback map of
[def-sc-field-extension]

$$
\rho^q_{k'/k}(C,\mathbf F_n):H^q(C_{\Et},\mathbf F_n)
\longrightarrow H^q((C_{k'})_{\Et},\mathbf F_n)
$$

is an isomorphism; if $C$ is proper it is compatible with the
identifications of [lem-sc-pic-proper-ntorsion] and
[lem-sc-genus-invariant], and if $C$ is affine with the
identifications of [lem-sc-pic-affine].

## Proof

By [lem-sc-base-change-curve], $C_{k'}$ is a smooth separated
connected curve over $k'$.

*Proper case.* The nonvanishing cohomology groups of
[thm-sc-proper-cohomology] over $k$ and over $k'$ are
$\mathbf Z/n\mathbf Z$, $(\mathbf Z/n\mathbf Z)^{2g}$ and
$\mathbf Z/n\mathbf Z$, identified by $\theta_\zeta$
([lem-sc-primitive-root]: the image of $\zeta$ in $k'$ is
primitive), by $g(C_{k'})=g(C)$ ([lem-sc-genus-invariant])
and by the etale group scheme $J_C[n]$
([thm-av-final](b),(c): the canonical base change map
$J_C[n](k)\to J_C[n](k')$ is an isomorphism, and
$J_{C_{k'}}\cong(J_C)_{k'}$ by
[thm-sc-jacobian-representability]); these identifications are
compatible with the pullback maps $\rho^q$, because all maps
involved are the canonical base change maps and the Kummer long
exact sequence of [lem-sc-kummer-les] is natural in the base
field. Hence each $\rho^q$ is an isomorphism.

*Affine case.* For $H^0$: $\mu_n(k)=\mu_n(k')$
([lem-sc-primitive-root]). For $H^1$: by
[lem-sc-kummer-les] there are canonical exact sequences

$$
0\to\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}
\to H^1(C,\mu_n)\to\operatorname{Pic}(C)[n]\to0
$$

and the analogous one over $k'$, all maps being the canonical
pullbacks. The right-hand terms are identified by the argument
below (the quotient descriptions of [lem-sc-pic-affine]); the
left-hand terms are identified as follows. With the compactification
$\overline C$ and the finite deleted set $S=\overline C\setminus C$
(the same finite set over $k'$, as $S_{k'}=S$), a unit
$u\in\mathcal O_C(C)^\times$ is a function on $\overline C$ whose
divisor is supported on $S$, and the association
$u\mapsto\operatorname{div}(u)$ identifies
$\mathcal O_C(C)^\times/k^\times$ with the subgroup of the
degree-zero divisors supported on $S$ whose class in
$J_{\overline C}$ is zero. This subgroup is finitely generated free;
it is unchanged by base change $k\to k'$, because
$J_{\overline C}(k)\to J_{\overline C}(k')$ is injective, so a
degree-zero divisor supported at the same $k$-rational set $S$ is
principal over $k$ if and only if it is principal over $k'$. As
$k^\times$ and $k'^\times$ are both $n$-divisible, the natural maps

$$
\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}
\to\mathcal O_{C_{k'}}(C_{k'})^\times/
\mathcal O_{C_{k'}}(C_{k'})^\times{}^{\,n}
$$

are isomorphisms. The five lemma now shows that the
middle maps $H^1(C,\mu_n)\to H^1(C_{k'},\mu_n)$ are isomorphisms.
For the right-hand identification: under the quotient descriptions
of [lem-sc-pic-affine] for $C$ and
$C_{k'}$ (the compactification of $C_{k'}$ is
$\overline C_{k'}$ by [lem-sc-base-change-curve], and the
deleted set $S$ is the same finite set, since
$S_{k'}=S\otimes_kk'=S$), the pullback map is
$x+\Lambda\mapsto x+\Lambda$. This is an isomorphism on
$n$-torsion: injectivity is clear; for surjectivity, let
$y\in J_{\overline C}(k')$ with $ny\in\Lambda\subset J_{\overline C}(k)$; by divisibility of $J_{\overline C}(k)$
([thm-av-final](d)) there is $z\in J_{\overline C}(k)$ with $ny=nz$, so
$y-z\in J_{\overline C}[n](k')=J_{\overline C}[n](k)\subset J_{\overline C}(k)$ ([thm-av-final](c)), whence
$y\in J_{\overline C}(k)$. For $H^2$: both groups vanish
([lem-sc-brauer-zero] over $k$ and over $k'$), and for
$q>2$ both groups vanish by
[lem-sc-cohomological-dimension] (over $k$ and over
$k'$).
