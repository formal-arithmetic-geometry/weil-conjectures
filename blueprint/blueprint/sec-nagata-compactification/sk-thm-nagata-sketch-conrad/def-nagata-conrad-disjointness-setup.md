+++
id = "def-nagata-conrad-disjointness-setup"
kind = "definition"
title = "The disjointness situation (Conrad)"
order = 207
uses = ["def-nagata-global-blowup", "def-nagata-scheme-theoretic-image"]
+++
**Status.** Bypassed by the formalized route: Deligne's disjointness blow-up
is formalized as the single statement
`AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`,
which absorbs this step.

Consider open immersions $i\colon U\to V$ and $j\colon V\to X$, a morphism
$p\colon Z\to X$, a scheme $Y$ over $U$, and a quasi-compact immersion
$f\colon Y\to Z$ over $X$, so that the square

$$
(Y\xrightarrow{f}Z\xrightarrow{p}X)
\;=\;(Y\to U\xrightarrow{j\circ i}X)
$$

commutes; in particular $Y$ lies over $U$. Write $\overline Y$ for the scheme-theoretic image of $Y$ in $Z$
under $f$. Fix the following data.

1. A quasi-coherent ideal $\mathcal I_1$ on $X$ with
$\overline{V\setminus U}\subseteq V(\mathcal I_1)\subseteq X\setminus U$
as sets, and $T_1=V(\mathcal I_1^2)$, a square-zero thickening of
$V(\mathcal I_1)$.
1. A quasi-coherent ideal $\mathcal I_2$ on $X$ whose zero scheme
$T_2=V(\mathcal I_2)$ satisfies $T_2\subseteq T_1\cap(X\setminus V)$ as
sets.
1. The hypothesis that the closed subscheme
$p^{-1}(T_1)\cap\overline Y$ of $Z$ factors through the closed
subscheme $p^{-1}(T_2)$. Loosely: $p(p^{-1}(T_1)\cap\overline Y) \subseteq T_2\subseteq T_1\cap(X\setminus V)$, the first inclusion as
schemes and the second as sets.

Let $q\colon X'\to X$ be the blow-up of $X$ along $\mathcal I_1+\mathcal I_2$
and let $Y',Z',p'$ denote the base changes of $Y,Z,p$ along $q$.
