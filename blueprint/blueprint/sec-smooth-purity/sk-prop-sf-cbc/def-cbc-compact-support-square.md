+++
id = "def-cbc-compact-support-square"
kind = "definition"
title = "Compact-support base-change square"
order = 1527
uses = ["def-weil-compactifications-refinements", "def-weil-pbc-cartesian-square", "def-weil-pbc-scheme-conventions", "thm-nagata-compactification"]
+++
Let $S$ be a scheme and let

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{g}&Y
\end{array}
$$

be a cartesian square of
$S$-schemes with $f:X\to Y$
separated and of finite
type; no hypothesis on $g$ is made. A
*compactification of $f$* is a factorization

$$
X\xrightarrow{\ j\ }\overline X\xrightarrow{\ p\ }Y
$$

with $j$ an open immersion and $p$ a
proper $S$-morphism and
$pj=f$, as in
[def-weil-compactifications-refinements]; write
$c=(j,p)$. For the base change $g:Y'\to Y$, put

$$
\overline X'=\overline X\times_YY',\qquad
X'=X\times_YY'
$$

with the projections $\bar g':\overline X'\to\overline X$,
$p':\overline X'\to Y'$, $j':X'\hookrightarrow\overline X'$
(the base change of the open immersion), and
$g':X'\to X$; by the base-change stability in
[thm-nagata-compactification] the data $c'=(j',p')$ form a
compactification of $f'$.
