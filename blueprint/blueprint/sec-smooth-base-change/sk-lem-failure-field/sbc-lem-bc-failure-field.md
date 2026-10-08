+++
id = "sbc-lem-bc-failure-field"
kind = "lemma"
title = "A failure is detected on the generic fibre"
order = 1391
uses = ["sbc-def-base-change-map", "sbc-def-base-change-property", "sbc-lem-bc-injectivity", "sbc-lem-bc-minimal-counterexample", "sbc-lem-higher-direct-image-limit", "sbc-lem-thickening-etale-site"]
+++
With $f:X\to S$ and $n$ as in [sbc-def-base-change-property] assume for
some $q\geq1$ that $\mathrm{BC}(f,n,q')$ holds universally for all
$q'\leq q-1$, but $\mathrm{BC}(f,n,q)$ does not hold universally. Then there exist a commutative diagram

$$
\begin{array}{ccccc}
X & \longleftarrow & X' & \longleftarrow & Y\\
f\big\downarrow & & \big\downarrow f' & & \big\downarrow e\\
S & \longleftarrow & S' & \longleftarrow & \operatorname{Spec}K
\end{array}
$$

where $X'=X\times_SS'$, $Y=X'\times_{S'}\operatorname{Spec}K$, $S'$ is
an affine scheme, $K$ is a
field, and $\mathcal F$ is an abelian sheaf on
$\operatorname{Spec}K$ annihilated by $n$ such that

$$
f'^{-1}R^qg_*\mathcal F\longrightarrow R^qh_*e^{-1}\mathcal F
$$

is not an isomorphism. If $S$ is separated, then moreover
$S'\to S$ is an affine morphism.
(*Stacks Project, Lemma 59.88.6, [Tag `0F07`](https://stacks.math.columbia.edu/tag/0F07).*)

## Proof

Choose a counterexample, i.e. a morphism $S'\to S$ with base change
$f':X'=X\times_SS'\to S'$ for which $\mathrm{BC}(f',n,q)$ fails: a
quasi-compact quasi-separated $g:T\to S'$ with $Y=X'\times_{S'}T$ and
$\mathcal F$ annihilated by $n$ such that the map of
[sbc-def-base-change-map] is not an isomorphism. Being an isomorphism
is local on $X'$, and for an open $U\subset S'$ the formation of
$R^qg_*$, $R^qh_*$ and of the base-change map commutes with
restriction to $U$, $X'_U$ (restriction to an open is the pullback
along an etale morphism and the higher direct images are the
sheafified cohomology presheaves); so the map already fails to be an
isomorphism over some affine open $U\subset S'$ and we may replace
$S'$ by $U$, $T$ by $T\times_{S'}U$. Thus $S'$ is affine, and $T$,
being quasi-compact and quasi-separated over the affine $S'$, is
quasi-compact and quasi-separated. By
[sbc-lem-bc-injectivity] (for the base change $f'$ along $g$) the map
is injective, so there is a
geometric point $\bar x$ of $X'$ and an element $\xi$ of
$(R^qh_*e^{-1}\mathcal F)_{\bar x}$ not in the image of
$(f'^{-1}R^qg_*\mathcal F)_{\bar x}$. For a morphism
$\pi:T'\to T$ let $\mathcal F'=\pi^{-1}\mathcal F$ and define
$P(T')$ to be the property: the image $\xi'$ of $\xi$ in
$(R^qh'_*(e')^{-1}\mathcal F')_{\bar x}$ is not in the image of
$(f'^{-1}R^qg'_*\mathcal F')_{\bar x}$. We apply
[sbc-lem-bc-minimal-counterexample] to $P$.

- *(1) Thickenings.* By [sbc-lem-thickening-etale-site]
the etale site of a scheme and of a thickening of it are the
same, so the cohomology sheaves involved are unchanged and
$P(T'')$ iff $P(T')$.
- *(2) Limits.* For $T'=\varprojlim T_i$ with affine
transitions, $\mathcal F'$ is the colimit of the pullbacks of
$\mathcal F_i$, and
[sbc-lem-higher-direct-image-limit] gives
$\varinjlim R^qh'_{i,*}e_i^{-1}\mathcal F_i =R^qh'_*e'^{-1}\mathcal F'$ and the analogue for
$g'$-side; hence $P(T_i)$ for all $i$ implies $P(T')$.
- *(3) Closed–open split.* Let $T'$ be with $P(T')$ and
$Z\subset T'$ closed with quasi-compact complement $V$. Choose an
injection $j^{-1}\mathcal F'\to\mathcal J$ with $\mathcal J$ an
injective sheaf of $\mathbf Z/n\mathbf Z$-modules on $V$, where
$j:V\hookrightarrow T'$; then
$\mathcal F'\to j_*\mathcal J\oplus i_*i^{-1}\mathcal F'$ is
injective (check on stalks, with $i:Z\hookrightarrow T'$ the closed
immersion), so by
[sbc-lem-bc-injectivity] (2), for the base change $f'$ along
$g':T'\to S'$ (quasi-compact and quasi-separated since $T'$ is and $S'$
is affine), the image of $\xi'$ is nonzero in
the direct-sum cokernel for
$\mathcal G=j_*\mathcal J\oplus i_*i^{-1}\mathcal F'$. If it is
nonzero in the second summand, then, since
$i_*$ (also $i'_*$) is exact for closed immersions,
$R^qg'_*i_*i^{-1}\mathcal F'=R^q(g'\circ i)_*i^{-1}\mathcal F'$
and $R^qh'_*e'^{-1}i_*i^{-1}\mathcal F'=R^qh''_*e_Z^{-1} i^{-1}\mathcal F'$ (Grothendieck spectral sequence), so
$P(Z)$ holds. If it is nonzero in the first summand, then
applying, for every $a\leq q-1$, the property
$\mathrm{BC}(e',n,a)$ of the base change $e':Y'=X'\times_{S'}T'\to T'$
of $f$ (along $T'\to S'\to S$) to the square with horizontal side the
open immersion $j:V\to T'$ (quasi-compact as $V$ is quasi-compact and
$T'$ quasi-separated, and separated) (this is where the universal
cumulative hypothesis in all degrees $\leq q-1$ is used) gives
$e'^{-1}j_*\mathcal J=j'_*e_V^{-1}\mathcal J$ (degree $a=0$) and,
together with $R^aj_*\mathcal J=0$ for $a\geq1$ ($\mathcal J$ being
injective), the vanishing of the higher direct images
$R^aj'_*e_V^{-1}\mathcal J$ for $a=1,\dots,q-1$; the
relative Leray spectral sequence for $h'\circ j'$ shows
$$
R^qh'_*e'^{-1}j_*\mathcal J\longrightarrow
R^q(h'\circ j')_*e_V^{-1}\mathcal J
$$
is injective, and applying
[sbc-lem-bc-injectivity] (3), for the base change $f'$ along
$g'\circ j:V\to S'$, to
$j^{-1}\mathcal F'\subset\mathcal J$ gives $P(V)$.
- *(4) Empty scheme.* If $T'=\emptyset$ then $Y'=X'\times_{S'}T'=\emptyset$,
so $R^qh'_*(e')^{-1}\mathcal F'=0$; hence $\xi'=0$ lies in the image and
$P(\emptyset)$ fails.

By [sbc-lem-bc-minimal-counterexample], $P(\operatorname{Spec}K)$
holds for some field $K$ with a morphism $\operatorname{Spec}K\to T\to S'$,
which is the assertion, with $S'$ the affine scheme chosen at the start.
Finally, let $S$ be separated. Then the diagonal $S\to S\times S$ is a
closed immersion, hence affine, and any morphism from an affine
scheme to $S$ is affine: for $V\subset S$ affine open,
$S'\times_SV=(S'\times V)\times_{S\times S}S$ is affine over the affine
scheme $S'\times V$, hence affine; so $S'\to S$ is affine.
