+++
id = "lem-pc-flat-rf-open"
kind = "lemma"
title = "The open locus of invertible $Rf_*$"
order = 682
uses = ["def-pc-derived-category", "def-pc-derived-pullback", "def-pc-perfect-complex", "lem-pc-flat-complex-derived-pullback", "lem-pc-perfect-locus", "lem-pc-rf-perfect-base-change", "thm-pc-semicontinuity-base-change"]
+++
(Derived Categories of Schemes, Lemma 36.32.3, Tag
[0B9S](https://stacks.math.columbia.edu/tag/0B9S).) Let
$f:X\to S$ be a proper morphism of finite presentation and let $\mathcal{F}$ be an
$\mathcal{O}_X$-module of finite presentation, flat over $S$. Fix $i,r\in\mathbb{Z}$.
Then there exists an open subscheme $U\subset S$ such that a morphism
$T\to S$ factors through $U$ if and only if $Rf_{T,*}\mathcal{F}_T$ is isomorphic
to a finite locally free $\mathcal{O}_T$-module of rank $r$ placed in degree $i$.

## Proof

Put $E=Rf_*\mathcal{F}\in D(\mathcal{O}_S)$ (see [def-pc-derived-category]).
By [lem-pc-rf-perfect-base-change], $E$ is perfect and for every
$g:T\to S$ the canonical map $Lg^*E\to Rf_{T,*}\mathcal{F}_T$ is an
isomorphism, with $Lg^*$ the [def-pc-derived-pullback]. For $s\in S$
write $\beta^q(s)=\dim_{\kappa(s)}H^q(X_s,\mathcal{F}_s)$.

*The locus.* Let $U\subseteq S$ be the set of points $s$ with
$\beta^q(s)=0$ for all $q\neq i$ and $\beta^i(s)=r$. We show $U$ is
open. Fix $t\in S$. As in the proof of
[thm-pc-semicontinuity-base-change], by [def-pc-perfect-complex] there is
an affine open $V=\operatorname{Spec}(A)\ni t$ on which $E|_V$ is
represented by a bounded complex
$K:\;0\to K^a\to\cdots\to K^b\to0$ with $K^q\cong A^{n_q}$, and for
$s\in V$, since the terms of $K$ are flat,
[lem-pc-flat-complex-derived-pullback] and the base-change isomorphism
give

$$
H^q(X_s,\mathcal{F}_s)\cong H^q(K\otimes_A\kappa(s)).
$$

In particular $\beta^q\equiv0$ on $V$ for $q\notin[a,b]$, so on $V$ only
the finitely many conditions with $q\in[a,b]$ matter. By
[thm-pc-semicontinuity-base-change](2) each $\beta^q$ is upper
semicontinuous, so

$$
W=\{s\in V:\ \beta^q(s)\le0\ (q\neq i,\ a\le q\le b),\ \beta^i(s)\le r\}
$$

is a finite intersection of open subsets of $V$, hence open. For $s\in W$
the complex $K\otimes_A\kappa(s)$ of finite dimensional vector spaces has
cohomology only in degree $i$, so

$$
(-1)^i\beta^i(s)=\sum_q(-1)^q\dim_{\kappa(s)}H^q(K\otimes_A\kappa(s))
=\sum_q(-1)^qn_q ,
$$

which does not depend on $s\in V$. Hence $\beta^i$ is constant on $W$,
and $U\cap V$ is either $W$ or empty. In either case it is open, and
since such $V$ cover $S$, $U$ is open.

*The functorial characterization.* Let $U_E$ be the open subscheme
attached to the perfect object $E$ and to $i,r$ by [lem-pc-perfect-locus].
A point $s\in S$ lies in $U_E$ iff $g_s:\operatorname{Spec}\kappa(s)\to S$
factors through $U_E$, i.e. iff
$Lg_s^*E\cong Rf_{s,*}\mathcal{F}_s$ is isomorphic to $\kappa(s)^{r}$
placed in degree $i$. As $\operatorname{Spec}\kappa(s)$ is a point, the
cohomology of $Rf_{s,*}\mathcal{F}_s$ is $H^*(X_s,\mathcal{F}_s)$, and a
complex over a field is quasi-isomorphic to the sum of its shifted
cohomology groups; so this holds iff $s\in U$. Thus $U=U_E$ as sets, and
we give $U$ the open subscheme structure. By [lem-pc-perfect-locus] a
morphism $g:T\to S$ factors through $U$ iff $Lg^*E$ is isomorphic to a
finite locally free $\mathcal{O}_T$-module of rank $r$ placed in degree
$i$, i.e. by the base-change isomorphism iff $Rf_{T,*}\mathcal{F}_T$ is.
On $U$ itself this gives (Nakayama, as in [lem-pc-perfect-locus]) that
$Rf_*\mathcal{F}|_U$ is locally a free module of rank $r$ in degree $i$;
no reducedness of $S$ is needed.
