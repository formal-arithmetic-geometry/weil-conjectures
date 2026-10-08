+++
id = "lem-chow-preimage"
kind = "lemma"
title = "The preimages of the members of the cover"
order = 1059
lean = ["AlgebraicGeometry.ChowGraph.isProper_morphismRestrict_modificationMap", "AlgebraicGeometry.ChowGraph.preimage_modificationMap"]
uses = ["def-nagata-affine-proj", "def-nagata-dense-compactification", "def-nagata-projective-space-base-change", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-weil-pbc-scheme-conventions", "lem-chow-agree-on-dense-open", "lem-chow-closed-model", "lem-chow-glue", "lem-chow-graph", "lem-chow-tuple-immersion", "lemma-nagata-dense-flat-pullback", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-projective-space-base-change-proper", "lemma-nagata-proper-to-separated-target", "lemma-nagata-scheme-image-ideal-qc"]
+++
In the situation of [lem-chow-glue] one has $\pi^{-1}(U_i)=V_i$ for every
$i$. Consequently $\pi^{-1}(U_i)\to U_i$ is the proper morphism
$p_i|_{V_i}$.

## Proof

The inclusion $V_i\subseteq\pi^{-1}(U_i)$ holds because $\pi|_{V_i}=p_i|_{V_i}$
takes values in $U_i$. The morphism $p_i|_{V_i}\colon V_i\to U_i$ is proper,
being the base change of the proper morphism $p_i$ along the open immersion
$U_i\to Z_i$. The open subscheme $\pi^{-1}(U_i)\subseteq Z$ is separated over
$S$, hence $\pi^{-1}(U_i)\to U_i$ is separated. Applying 01W6
to the commutative triangle formed by $V_i\to\pi^{-1}(U_i)$ and the two
morphisms to $U_i$, we conclude that $V_i\to\pi^{-1}(U_i)$ is universally
closed; in particular $V_i$ is closed in $\pi^{-1}(U_i)$. On the other hand
$U\subseteq V_i$ and $U$ is dense in the open subscheme
$\pi^{-1}(U_i)\subseteq Z$, so $V_i$ is dense in $\pi^{-1}(U_i)$. Being closed
and dense, $V_i=\pi^{-1}(U_i)$.

## Detailed form

In the situation of [lem-chow-glue],

$$
 \pi^{-1}(U_i)=V_i
$$

for every $i$; consequently the restriction $\pi^{-1}(U_i)\to U_i$ is the
morphism $p_i|_{V_i}$, which is proper by
[lem-chow-graph] (ii) and the stability of properness
under base change.

## Proof

The inclusion $V_i\subseteq\pi^{-1}(U_i)$ holds because $\pi|_{V_i}=p_i|_{V_i}$
maps $V_i$ into $U_i$ ([lem-chow-glue]).

*Step 1: $\pi$ is separated.* Each $p_i|_{V_i}:V_i\to U_i$ is proper by
[lem-chow-graph] (ii) (its properness is stable under
the base change along the open immersion $U_i\to Z_i$, Stacks Project,
Morphisms, Lemma 29.42.5, Tag
[01W4](https://stacks.math.columbia.edu/tag/01W4)), hence separated; since
separatedness is local on the source and the $V_i$ cover $X'$, the morphism
$\pi$ is separated. Hence its base change
$\pi^{-1}(U_i)=X'\times_XU_i\to U_i$ along the open immersion $U_i\to X$ is
separated.

*Step 2: $V_i$ is closed in $\pi^{-1}(U_i)$.* Apply Stacks Project,
Morphisms, Lemma 29.42.7 (Tag
[01W6](https://stacks.math.columbia.edu/tag/01W6)) to the diagram whose
composite $V_i\to\pi^{-1}(U_i)\to U_i$ is the proper morphism $p_i|_{V_i}$ and
whose second member $\pi^{-1}(U_i)\to U_i$ is separated: the lemma says that
the morphism $V_i\to\pi^{-1}(U_i)$ is proper, hence closed, so its image
(which is $V_i$ itself) is closed in $\pi^{-1}(U_i)$.

*Step 3: $V_i$ is dense in $\pi^{-1}(U_i)$.* By
[lem-chow-graph] (i), $U$ is scheme-theoretically dense
in $\widetilde X$; since $U\subseteq V_i$ and
$\pi^{-1}(U_i)\subseteq\widetilde X$ is open, the closure of $V_i$ in
$\pi^{-1}(U_i)$ is all of $\pi^{-1}(U_i)$. Steps 2 and 3 give
$V_i=\pi^{-1}(U_i)$.
