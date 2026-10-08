+++
id = "sk-cor-nagata-sketch-proper-extension"
kind = "section"
title = "Extension to a proper target"
order = 222
uses = ["sk-thm-nagata-sketch-conrad"]
lean = ["AlgebraicGeometry.exists_admissibleBlowup_extend_of_isProper"]
+++
*Corollary (sketch).*

If $X$ is qcqs over $S$, $U\subseteq X$ is a dense quasi-compact open,
and $Y\to S$ is proper, every $S$-map $U\to Y$ extends to a map
$X'\to Y$ after a $U$-admissible blow-up.

## Proof

Take $V=U$. The resulting graph $W\hookrightarrow X'\times_SY$
is closed, so $W\to X'$ is both proper and an open immersion.
Its image is dense, hence all of $X'$.

Uses: [sk-thm-nagata-sketch-conrad]
