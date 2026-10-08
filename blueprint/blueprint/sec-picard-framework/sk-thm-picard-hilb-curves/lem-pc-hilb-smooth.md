+++
id = "lem-pc-hilb-smooth"
kind = "lemma"
title = "Hilbert schemes of curves are smooth"
order = 788
uses = ["def-pc-morphism-conventions", "lem-pc-hilb-addition"]
+++
(Picard Schemes of Curves, Lemma 44.3.5, Tag
[0B9H](https://stacks.math.columbia.edu/tag/0B9H).) Let $X\to S$ be
a separated smooth morphism of relative dimension $1$ such that
all the functors $\operatorname{Hilb}^e_{X/S}$ are representable. Then
$\underline{\operatorname{Hilb}}^d_{X/S}$ is smooth over $S$ of relative dimension $d$
(for a smooth proper curve $X$ over a field $k$,
$\underline{\operatorname{Hilb}}^d_{X/k}$ is smooth of dimension $d$ over $k$).

## Proof

*The cases $d=0,1$.* $\operatorname{Hilb}^0_{X/S}(T)$ has exactly one element
(the empty closed subscheme of $X_T$, finite locally free of degree
$0$; it is defined by the unit ideal; the pullback along $T'\to T$ is the empty
subscheme): the representing scheme is $S$, which is smooth over $S$
of relative dimension $0$. $\operatorname{Hilb}^1_{X/S}(T)$ consists of the closed
subschemes $Z\subseteq X_T$ finite locally free of degree $1$: such a
$Z$ is the graph of a unique morphism $T\to X$ (the projection
$Z\to T$ is an isomorphism, being finite locally free of degree $1$
and the closed immersion gives the section $T\to X$: the composite
$T\stackrel{\sim}{\leftarrow}Z\hookrightarrow X_T$ is the desired
morphism; conversely the graph of a morphism $T\to X$ is a closed
subscheme finite locally free of degree $1$ because $X\to S$ is
separated, the graph being closed): hence $\operatorname{Hilb}^1_{X/S}=X$ (the
functor is represented by $X$), which is smooth of relative dimension
$1$ over $S$. (For a non-separated $X\to S$ the graph of a morphism
is not closed in general: one then uses the ``closed graph'' via the
immersion-theoretic twist; the classical statement is used here in the
separated case, which holds in all applications of this lemma.)

*Induction.* Assume $\underline{\operatorname{Hilb}}^d_{X/S}$ is smooth over
$S$ of relative dimension $d$. Put $H_d:=\underline{\operatorname{Hilb}}^d_{X/S}$
and let

$$
\pi:H_d\times_SX\;\longrightarrow\;H_{d+1}
$$

be the morphism of [lem-pc-hilb-addition], finite locally free of
degree $d+1$. The source $H_d\times_SX$ is smooth over $S$ of
relative dimension $d+1$: base changes and compositions of smooth
morphisms are smooth (the standard statements; in the
[def-pc-morphism-conventions] under the local
characterization of smoothness), so the source is smooth over
$H_d$ (the projection is the base change of the smooth
$X\to S$ along $H_d\to S$) and then over $S$; the relative dimension
is $d+1$ (relative dimensions add for composites, and base change of
$X/S$ of relative dimension $1$ keeps relative dimension $1$).
Since $\pi$ is finite locally free of degree $d+1\ge1$, it is
surjective (a finite locally free morphism of positive degree has
nonempty fibres: over a point $t$ of the target the fibre is a
finite flat algebra of rank $d+1\ge1$ over $\kappa(t)$, hence nonzero,
so the fibre is a nonempty scheme) and faithfully flat. Smoothness
descends along faithfully flat coverings: the classical descent
``smoothness is of fpqc local nature on the target''
(Descent, Lemma 35.14.5: a morphism $Y\to S$ such that there is a
surjective flat morphism of finite presentation $Y'\to Y$ with
$Y'\to S$ smooth, has $Y\to S$ smooth; the statement in the precise
form used here: the faithfully flat descent of the smoothness
property, which is a local property in the fpqc topology), so
$H_{d+1}\to S$ is smooth. The relative dimension: $\pi$ is finite,
hence proper, and surjective, so $\dim H_{d+1}=\dim(H_d\times_SX)= d+1$ (a finite surjective morphism between schemes of finite type
over $S$ preserves the dimension; the dimension of the source over
$S$ is $d+1$ since it is smooth of relative dimension $d+1$), i.e. $H_{d+1}$ is smooth of relative dimension $d+1$ over $S$. This
proves the lemma.
