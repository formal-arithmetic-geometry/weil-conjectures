+++
id = "lemma-nagata-immersion-shrink-to-closed-exists"
kind = "lemma"
title = "Existence of a quasi-compact closed-immersion neighbourhood"
order = 384
lean = ["AlgebraicGeometry.Scheme.Hom.exists_isCompact_isClosedImmersion"]
uses = ["lem-weil-pbc-closed-immersion-from-composite"]
+++
Let $i\colon X\to Y$ be an immersion with $X$ quasi-compact. There is a
quasi-compact open $W\subseteq Y$ containing $i(X)$ such that $X\to W$ is a
closed immersion. (No quasi-separatedness assumption on $Y$ is needed; the
formalised statement drops it.)

## Proof

Factor the immersion as a closed immersion $X\hookrightarrow U$ followed by
an open immersion $U\hookrightarrow Y$. The image of the quasi-compact
scheme $X$ is quasi-compact in $U$. Cover it by affine opens of $Y$
contained in $U$, and choose a finite subcover $V_1,\ldots,V_n$. Their
union $W=\bigcup_rV_r$ is a quasi-compact open of $Y$, contains $i(X)$,
and is contained in $U$. Base-changing the closed immersion
$X\hookrightarrow U$ along $W\hookrightarrow U$ gives a closed immersion
$X\times_UW\hookrightarrow W$. Because the image of $X$ lies in $W$, the
first projection identifies $X\times_UW$ with $X$, so the induced map
$X\to W$ is a closed immersion.
