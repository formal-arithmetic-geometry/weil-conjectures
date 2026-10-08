+++
id = "lem-chow-glue"
kind = "lemma"
title = "Gluing the projections"
order = 1058
lean = ["AlgebraicGeometry.ChowGraph.modificationMap", "AlgebraicGeometry.ChowGraph.projPreimage", "AlgebraicGeometry.ChowGraph.projRestrict"]
uses = ["def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-agree-on-dense-open", "lem-chow-closed-model", "lem-chow-graph", "lem-chow-tuple-immersion", "lemma-nagata-dense-flat-pullback", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
In the situation of [lem-chow-graph] put $V_i:=p_i^{-1}(U_i)$ and
$X':=V_1\cup\dots\cup V_m$, an open subscheme of $Z$. Then the morphisms
$p_i|_{V_i}\colon V_i\to U_i\subseteq X$ glue to a morphism of $S$-schemes

$$
\pi\colon X'\longrightarrow X
$$

with $\pi|_{V_i}=p_i|_{V_i}$, and $\pi|_U=\mathrm{id}_U$.

In the formalisation $V_i$ is the preimage under $p_i$ of the image of $U_i$ in
$Z_i$, and $V_i$, $U$ and $X'$ are all opens of $Z$; the last assertion reads
that the composition of the open immersion $U\to X'$ with $\pi$ is the inclusion
$U\to X$.

## Proof

By [lem-chow-graph](3) we have $U\subseteq V_i$ for every $i$, and
$p_i|_U\colon U\to U_i\subseteq X$ is the inclusion. Since $U$ is
scheme-theoretically dense in $Z$ and $V_i\cap V_j\subseteq Z$ is open, $U$ is
scheme-theoretically dense in $V_i\cap V_j$. The two morphisms
$p_i|_{V_i\cap V_j}$ and $p_j|_{V_i\cap V_j}$ into $X$ agree on $U$, and
$X\to S$ is separated, so they are equal by
[lem-chow-agree-on-dense-open]. Hence the $p_i|_{V_i}$ glue to
$\pi\colon X'\to X$, and $\pi|_U=\mathrm{id}_U$.

## Detailed form

In the situation of [lem-chow-graph], put

$$
 V_i:=p_i^{-1}(U_i)\subseteq\widetilde X
$$

and $X':=V_1\cup\dots\cup V_m$. Then for all $i,j$, $U\subseteq V_i\cap V_j$
is scheme-theoretically dense, and the morphisms $p_i|_{V_i}:V_i\to U_i$ glue
to a morphism

$$
 \pi:X'\longrightarrow X
$$

over $Y$. (Here $X$ is identified with the separated scheme in which the
affine opens $U_i\subseteq X$ sit; $X$ is separated over $Y$ since $X\to Y$ is
proper.) One has $\pi|_U=\operatorname{id}_U$.

## Proof

Since $U\subseteq\widetilde X$ is scheme-theoretically dense by
[lem-chow-graph] (i), and $V_i\cap V_j$ is an open
subscheme of $\widetilde X$, the open $U\subseteq V_i\cap V_j$ is
scheme-theoretically dense in $V_i\cap V_j$ (restriction of density to opens).
The two morphisms $p_i|_{V_i\cap V_j}$ and $p_j|_{V_i\cap V_j}$ take values in
$U_i\cap U_j\subseteq X$ and agree on $U$; by
[lem-chow-agree-on-dense-open] (whose hypotheses hold: $X$ is
separated over $Y$ because it is proper over $Y$), they agree. Hence the
morphisms $p_i|_{V_i}$ are compatible on overlaps and glue to a morphism
$\pi:X'\to X$ (gluing of schemes coincides with gluing of morphisms), and to
see $\pi|_U=\operatorname{id}_U$: each $p_i|_{V_i}$ restricts on $U\subseteq
V_i$ to the identity on $U$ (the open immersion $U\hookrightarrow U_i$ and the
composite $U\hookrightarrow\widetilde X\hookrightarrow Z_i$ are the same
morphism by construction of the diagonal morphism $j$ in
[lem-chow-graph]).
