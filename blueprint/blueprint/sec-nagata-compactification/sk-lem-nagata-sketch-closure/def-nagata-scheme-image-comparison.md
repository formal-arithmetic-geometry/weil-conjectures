+++
id = "def-nagata-scheme-image-comparison"
kind = "definition"
title = "Comparison map for a closed factorization"
order = 70
lean = ["AlgebraicGeometry.IsClosedImmersion.lift"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-of-closed-immersion"]
+++
Suppose $g$ is supplied with a factorization
$T\xrightarrow{h}Z\xrightarrow{z}Y$, where $z$ is a closed immersion.
Define

$$
c_{g,Z}\colon\operatorname{SIm}(g)\longrightarrow Z
$$

from the containment of the ideal defining $Z$ in the kernel ideal defining
$\operatorname{SIm}(g)$.
