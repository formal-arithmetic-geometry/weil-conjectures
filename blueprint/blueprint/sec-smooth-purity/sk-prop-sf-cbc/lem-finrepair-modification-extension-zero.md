+++
id = "lem-finrepair-modification-extension-zero"
kind = "lemma"
title = "Extension by zero under a proper modification"
order = 1594
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-weil-pbc-extension-by-zero", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $\pi:Y\to X$ be proper and let $j:U\hookrightarrow X$ be open
such that $\pi^{-1}(U)\to U$ is an isomorphism, with morphisms as in
[def-weil-pbc-scheme-conventions].
Write $j':U'=\pi^{-1}(U)\hookrightarrow Y$.
For an etale $\Lambda$-sheaf $G$ on $U$, let $G'$ be its
pullback to $U'$. Then

$$
\pi_*j'_!G'\simeq j_!G,\qquad R^q\pi_*j'_!G'=0\quad(q>0),
$$

using the inverse image and extension by zero of
[def-weil-pbc-inverse-image], [def-weil-pbc-extension-by-zero].

## Proof

Extension by zero commutes with pullback here: the map
$\pi^*j_!G\to j'_!G'$ is obtained from its identity restriction on
$U'$, and is an isomorphism on every geometric stalk.
Over a point of $U'$ both stalks are the stalk of $G$;
outside $U'$ both are zero.
This uses the stalk descriptions in
[def-weil-pbc-inverse-image], [def-weil-pbc-extension-by-zero]
and conservativity in
[lemma-weil-pbc-geometric-stalk-conservative].
Adjunction supplies $j_!G\to\pi_*j'_!G'$.

At a geometric point $\bar x$ of $U$, the fibre of $\pi$ is
one geometric point and the restricted sheaf is $G_{\bar x}$.
At a geometric point of $X\setminus U$, the entire fibre is
disjoint from $U'$, and the restricted sheaf is zero.
The proper geometric-fibre formula of
[cor-weil-pbc-geometric-fiber-finite] therefore identifies
the displayed adjunction morphism with an isomorphism on all
stalks, and makes every positive-degree stalk $R^q\pi_*j'_!G'$
zero. Apply
[lemma-weil-pbc-geometric-stalk-conservative] once more.
