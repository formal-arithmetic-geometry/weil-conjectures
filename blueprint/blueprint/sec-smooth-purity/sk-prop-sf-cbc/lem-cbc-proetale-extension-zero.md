+++
id = "lem-cbc-proetale-extension-zero"
kind = "lemma"
title = "Extension by zero on the pro-etale site"
order = 1582
uses = ["def-weil-extension-by-zero", "def-weil-pbc-derived-categories", "def-weil-pbc-proetale-site", "def-weil-pbc-scheme-conventions"]
+++
For an open immersion
$j:U\hookrightarrow X$, extension by zero on the small pro-etale
site (the functor $j_!$ of [def-weil-extension-by-zero])
is the exact left adjoint of $j^{-1}$, acts degreewise, and is
characterized by the same stalk prescription as the etale one,

$$
(j_!K)_{\bar x}=
\begin{cases}
K_{\bar x},&\bar x\text{ lies in }U,\\
0,&\bar x\text{ lies in }X\setminus U,
\end{cases}
$$

for a complex $K$ of pro-etale sheaves and a geometric point
$\bar x$ of $X$; it is compatible with restriction of scalars
along a finite coefficient ring.

## Proof

The exactness and the left-adjoint property are part of
[def-weil-extension-by-zero], which is stated on the pro-etale
site. For the stalk description, the category of weak etale
neighbourhoods of $\bar x$ in
[def-weil-pbc-proetale-site] is filtered, and the
subcategory of the neighbourhoods that factor through the open
subscheme $U$ is cofinal in the neighbourhoods of $\bar x$ when
$\bar x\in U$, and empty otherwise; hence the stalk formula, and
the degreewise property of [def-weil-pbc-derived-categories]
follows from the explicit cofinality, the compatibility with
restriction of scalars being the naturality of the construction in
the coefficient ring.
