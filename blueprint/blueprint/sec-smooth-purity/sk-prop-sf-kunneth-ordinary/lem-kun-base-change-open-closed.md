+++
id = "lem-kun-base-change-open-closed"
kind = "lemma"
title = "Base change for open-closed immersions"
order = 1750
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-underived-exchange", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $j:U\to X$ be both an open and a closed immersion of schemes
and let $g:Y\to X$ be a morphism, forming the
cartesian square

$$
\begin{array}{ccc}
Y\times_XU&\xrightarrow{\;h\;}&Y\\
\Big\downarrow{\scriptstyle p}&&\Big\downarrow{\scriptstyle g}\\
U&\xrightarrow{\;j\;}&X .
\end{array}
$$

Then for every abelian sheaf $F$ on $U_{\Et}$ the base change map
$g^{-1}j_*F\to h_*p^{-1}F$ of
[def-weil-pbc-underived-exchange] is an isomorphism.

## Proof

Fix a geometric point $\bar y$ of $Y$ with image $\bar x=g(\bar y)$. If $x\in U$, the stalk of $g^{-1}j_*F$ at $\bar y$ is
$F_{\bar x}$, the universal property of the pullback in the
cartesian square identifying the inverse images along $g\circ j$
with $F_{\bar x}$; the same holds for $h_*p^{-1}F$. If $x\notin U$, then $X\setminus U$ is an open neighbourhood of $x$ because
$j$ is a closed immersion, and every etale source $W\to X$ with a
lift of $\bar x$ has $W\times_XU$ empty over that component, so
both stalks are zero: $j_*F$ has zero sections over an open
neighbourhood of $x$, and $p^{-1}F$ similarly. The map is an
isomorphism on all stalks, hence an isomorphism by
lem:weil-pbc-geometric-stalk-conservative.
