+++
id = "def-nagata-closed-subscheme-compactification"
kind = "definition"
title = "Closed-subscheme compactification construction"
order = 83
lean = ["AlgebraicGeometry.Compactification.ofIsClosedImmersion"]
uses = ["def-nagata-compactification", "def-nagata-immersion-compactification", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-image", "lemma-nagata-open-immersion-qc-over-separated-target"]
+++
Let $i\colon X\hookrightarrow X'$ be closed over $S$ and fix a
compactification $C'=(X'\to\overline X'\to S)$. Define
$\mathsf{Closed}(i,C')$ by taking the scheme-theoretic image
$\overline X=\operatorname{SIm}(X\to\overline X')$ and the factorization

$$
X\longrightarrow\overline X\hookrightarrow\overline X'\longrightarrow S.
$$
