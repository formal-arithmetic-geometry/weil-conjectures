+++
id = "def-kun-bc-property"
kind = "definition"
title = "The base-change property $BC(f,n,q_0)$"
order = 1669
uses = ["def-kun-cd", "def-kun-unbounded-exchange", "def-weil-pbc-scheme-conventions", "sbc-def-base-change-map", "sbc-def-base-change-property"]
+++
Let $f:X\to S$ be a morphism of schemes, $n\ge1$, and
$q_0\ge0$. Say *$BC(f,n,q_0)$ holds* if for every
commutative diagram

$$
\begin{array}{ccccc}
X&\longleftarrow&X'&\longleftarrow&Y\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{\scriptstyle f'}&\Big\downarrow{\scriptstyle e}\\
S&\longleftarrow&S'&\longleftarrow&T
\end{array}
$$

with $X'=X\times_SS'$, $Y=X'\times_{S'}T$, $g:T\to S'$
quasi-compact and
quasi-separated, $X'\to T$ (resp. $h:Y\to X'$) the resulting
projection, $\Lambda=\kunZn$ coefficients, and every abelian sheaf
$F$ on $T_{\Et}$ annihilated by $n$, the exchange morphism of
[def-kun-unbounded-exchange] is an
isomorphism on $q$-th cohomology sheaves for all $q\le q_0$; those
cohomology sheaves of the exchange morphism are the ones computed in
[lem-kun-bc-map-on-cohomology]. The
cohomological-dimension predicate of [def-kun-cd] is understood
at finite coefficients. The predicate is related to the one of the
smooth-base-change chapter, [sbc-def-base-change-property], which is
defined with the derived exchange morphism of
[sbc-def-base-change-map] in a single degree $q$, for $n$ invertible
on $S$ and squares over $S$ itself: the present $BC(f,n,q_0)$ is the
cumulative form over all base changes, i.e. (for $n$ invertible on
$S$) the property $BC(f',n,q)$ of [sbc-def-base-change-property] for
every $q\le q_0$ and every base change $f':X'\to S'$ of $f$, read
with the unbounded exchange morphism of [def-kun-unbounded-exchange];
the two exchange morphisms agree on the bounded complexes to which both
apply. Here $n$ is not required to be invertible on $S$.
