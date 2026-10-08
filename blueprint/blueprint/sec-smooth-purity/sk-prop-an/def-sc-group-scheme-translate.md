+++
id = "def-sc-group-scheme-translate"
kind = "definition"
title = "Translations and conjugation"
order = 1964
uses = ["def-sc-group-scheme", "def-sc-group-scheme-subgroup"]
+++
Let $G$ be a group scheme over a field
$k$ with multiplication $m$, inverse $i$, unit $e$ and structure
morphism $p:G\to\Spec k$, and let $g\in G(k)$ be a $k$-point. The
*left translation* by $g$ is the composite

$$
L_g:G\xrightarrow{\ (g\circ p,\ \mathrm{id}_G)\ }G\times_kG
\xrightarrow{\ m\ }G,
$$

the *right translation* by $g$ is
$R_g=m\circ(\mathrm{id}_G,g\circ p)$, and *conjugation* by $g$
is $c_g=L_g\circ R_{g^{-1}}$. For a closed
subgroup scheme
$Z\subseteq G$ the *translate* $gZ$ is the image of the
composite $L_g\circ j$, where $j:Z\hookrightarrow G$ is the closed
immersion.
