+++
id = "sk-lem-nagata-sketch-graph"
kind = "section"
title = "Proper graph extension"
order = 241
uses = ["sk-lem-nagata-sketch-elimination", "sk-lem-nagata-sketch-image-transform"]
lean = ["AlgebraicGeometry.Compactification.nonempty_properExtension"]
+++
*Lemma (sketch).*

Let $U\to S$ be separated and of finite type, let $A\subseteq U$ be
a quasi-compact open, and fix a compactification $A\hookrightarrow X$.
After an $A$-admissible blow-up of $X$ there is an open
$A\subseteq V\subseteq X'$ and a proper map $\psi:V\to U$
extending $A\hookrightarrow U$, with $\psi^{-1}(A)=A$ and
$\psi|_A=\operatorname{id}_A$; see 0F3Z.

## Proof

Close the graph of $A$ in $X\times_SU$ and apply elimination to its
projection to $X$. Its strict transform becomes the open $V$ in $X'$.
By [sk-lem-nagata-sketch-image-transform], it is the new graph closure
in $X'\times_SU$, hence proper over $U$. Restriction of the image to
$A$ proves the last two assertions.

Uses: [sk-lem-nagata-sketch-elimination], [sk-lem-nagata-sketch-image-transform]
