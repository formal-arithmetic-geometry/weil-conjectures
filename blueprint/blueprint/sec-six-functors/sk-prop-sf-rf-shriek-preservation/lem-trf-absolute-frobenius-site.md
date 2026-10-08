+++
id = "lem-trf-absolute-frobenius-site"
kind = "lemma"
title = "Canonical trivialization of absolute Frobenius pullback"
order = 2075
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-trf-weakly-etale-between-objects", "lem-trf-weakly-etale-homeomorphism"]
+++
Let $X$ be a scheme in characteristic $p>0$. On its
small pro-etale site, the
derived pullback
along absolute $p$-power Frobenius $F_X$ has a canonical
trivialization $LF_X^*\simeq\operatorname{id}$. It commutes with
restriction to open subschemes and with its multiplicative iterates.
(Source for the input: [Stacks,
Tag 0F6W](https://stacks.math.columbia.edu/tag/0F6W), Lemma 37.64.15 – for a weakly etale $U\to X$ the relative
Frobenius $F_{U/X}:U\to U\times_{X,F_X}X$ is an isomorphism; the
trivialization of the derived pullback and its compatibilities with
restriction and with the iterates are the content of the proof below.)

## Proof

An object $v:V\to X$ of [def-weil-pbc-proetale-site] is weakly
etale. Its relative Frobenius is

$$
r_V=(F_V,v):V\longrightarrow V\times_{X,F_X}X.
$$

It is integral and universally bijective. For an affine ring map
$R\to B$, the corresponding map
$B\otimes_{R,F_R}R\to B$ sends $b\otimes a$ to $b^pv(a)$.
Every $b\in B$ satisfies the monic equation $T^p-b^p=0$ over the
image, proving integrality. For an algebraically closed field
$\Omega$, a homomorphism from the tensor product to $\Omega$
specifies maps $\beta:B\to\Omega$, $\alpha:R\to\Omega$ satisfying
$\beta(v(a))=\alpha(a)^p$. The unique lift to $B$ is
$b\mapsto\beta(b)^{1/p}$: it is a ring map and its restriction to
$R$ is $\alpha$. This proves universal bijectivity. The argument
is local on $X$ and $V$, so $r_V$ is a universal homeomorphism.

Its source and target are weakly etale over $X$; the target is a
base change of $v$. Thus [lem-trf-weakly-etale-between-objects]
shows that $r_V$ is weakly etale. For clarity, the geometric
factorization behind this Mathlib result is as follows. If
$f:U\to W$ is a map between weakly etale $X$-schemes, its graph
$\Gamma_f:U\to U\times_XW$ is the base change of
$\Delta_{W/X}$ along
$(f\circ\operatorname{pr}_U,\operatorname{pr}_W)$, so is flat.
The projection $U\times_XW\to W$ is flat as a base change of
$U\to X$. Their composite $f$ is flat. Moreover the square

$$
\begin{array}{ccc}
U&\xrightarrow{\operatorname{id}}&U\\
{\scriptstyle\Delta_f}\downarrow&&
\downarrow{\scriptstyle\Delta_{U/X}}\\
U\times_WU&\longrightarrow&U\times_XU
\end{array}
$$

is Cartesian: on a test scheme a point of its fiber product is
$(u,(u_1,u_2))$ with $(u,u)=(u_1,u_2)$, hence is uniquely
$(u,(u,u))$. Therefore $\Delta_f$ is flat as well. These are
exactly the flatness conditions in
[def-weil-scheme-morphism-properties].
Applying [lem-trf-weakly-etale-homeomorphism] now makes
$r_V$ an isomorphism.

The $r_V$ commute with all morphisms of site objects. Consequently
the base-change functor $V\mapsto V\times_{X,F_X}X$ is naturally
isomorphic to the identity and preserves its coverings. On sheaves,
the inverses of the restriction maps along $r_V$ give
$\mathcal F(V)\simeq(F_{X*}\mathcal F)(V)$. Taking left adjoints
gives $F_X^*\simeq\operatorname{id}$. Both functors are exact,
so the same maps on complexes give the derived assertion with
[def-weil-derived-pullback-tensor-hom]. Restricting the maps
$r_V$ to an open gives the same relative Frobenius there.
Composing them gives relative $p^m$-power Frobenius, proving the
restriction and iteration assertions.

*Recorded in advance* from chapter *The trace formula* of the source.
