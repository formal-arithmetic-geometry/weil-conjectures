+++
id = "def-weil-pbc-scheme-conventions"
kind = "definition"
title = "Scheme and morphism conventions"
order = 2
+++
Let $f:X\to Y$ be a morphism of schemes. It is *quasi-compact* if the
preimage of every affine open of $Y$ is quasi-compact, and *quasi-separated*
if its diagonal $X\to X\times_YX$ is quasi-compact. A scheme is *affine* if
it is isomorphic to $\operatorname{Spec}A$ for a commutative ring $A$. The
morphism $f$ is *separated* if its diagonal is a closed immersion, of *finite
type* if it is quasi-compact and every affine open of $Y$ is covered by
finitely many affine opens of $X$ whose coordinate rings are finitely
generated over the coordinate ring of the corresponding affine open of $Y$,
and of *finite presentation* if the same holds with finitely presented
algebras. It is *surjective* if it is surjective on underlying topological
spaces, an *open immersion* if it identifies $X$ with an open subscheme of
$Y$, and a *closed immersion* if it is affine and is induced locally by a
surjective ring homomorphism. It is an *immersion* if it factors as a closed
immersion followed by an open immersion (equivalently, as an open immersion
followed by a closed immersion). It is *universally closed* if every base
change of $f$ is a closed map, and *proper* if it is separated, of finite
type, and universally closed. It is *finite* if it is affine and
$f_*\mathcal O_X$ is a finite $\mathcal O_Y$-algebra, and *integral* if it is
affine and $f_*\mathcal O_X$ is integral over $\mathcal O_Y$. It is
*radicial* if for every field $K$ the map $X(K)\to Y(K)$ is injective, and a
*universal homeomorphism* if every base change of $f$ is a homeomorphism of
underlying spaces. It is *flat* if every induced local-ring map is flat, and
*unramified* if it is locally of finite type and its diagonal is an open
immersion. It is *etale* if it is locally of finite presentation, flat, and
unramified, and *weakly etale* if it is flat and its diagonal is flat.

For $y\in|Y|$, the *geometric fiber* over $y$ is

$$
 X_{\bar y}=X\times_Y\operatorname{Spec}\overline{\kappa(y)},
$$

where $\overline{\kappa(y)}$ is a chosen algebraic closure of the residue
field $\kappa(y)$. A *geometric point* of $Y$ is a morphism $\bar
y:\operatorname{Spec}\Omega\to Y$ with $\Omega$ algebraically closed. A
subset of a scheme is *locally closed* if it is the intersection of an open
and a closed subset, and *constructible* if it is a finite union of locally
closed subsets; a *locally closed constructible subscheme* is a subscheme
whose underlying set is locally closed and constructible. A topological space
is *spectral* if it is quasi-compact, quasi-separated, sober, and has a basis
of quasi-compact opens.
