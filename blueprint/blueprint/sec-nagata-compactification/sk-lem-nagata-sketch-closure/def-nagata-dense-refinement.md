+++
id = "def-nagata-dense-refinement"
kind = "definition"
title = "Dense-refinement construction"
order = 81
lean = ["AlgebraicGeometry.Compactification.denseRefinement"]
uses = ["def-nagata-compactification", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-scheme-image-ideal-qc"]
+++
For a compactification $C=(X\xrightarrow{j}\overline X\to S)$, define
$\mathsf{Dense}(C)$ by replacing $\overline X$ with
$\operatorname{SIm}(j)$ and using $j^{\mathrm{im}}$ as its first map.
