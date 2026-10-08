+++
id = "def-nagata-graph-extension"
kind = "definition"
title = "Graph-extension construction"
order = 242
lean = ["AlgebraicGeometry.Compactification.ProperExtension"]
uses = ["def-nagata-admissible-blowup", "def-nagata-compactification", "def-nagata-elimination-indeterminacy", "def-nagata-global-blowup", "def-nagata-scheme-theoretic-image", "prop-nagata-global-blowup-cover-independent"]
+++
Let $U\to S$ be separated and of finite type, let $V\subseteq U$ be
quasi-compact, and fix a compactification
$V\hookrightarrow Y\to S$. Define

$$
Z_V=\operatorname{SIm}
\bigl(V\xrightarrow{(j,\,\mathrm{incl})}Y\times_SU\bigr).
$$

Apply [def-nagata-elimination-indeterminacy] to the first projection
$Z_V\to Y$ over $V$. Denote the resulting blow-up by
$Y^{\mathrm{gr}}\to Y$ and the open strict transform by
$Z_V^{\mathrm{st}}\hookrightarrow Y^{\mathrm{gr}}$. Define

$$
V^{\mathrm{gr}}\subseteq Y^{\mathrm{gr}}
\quad\text{to be the represented open subscheme }Z_V^{\mathrm{st}},
\qquad
\psi^{\mathrm{gr}}\colon V^{\mathrm{gr}}\longrightarrow U
$$

by transporting the second projection
$Z_V^{\mathrm{st}}\to U$ across the open-immersion identification.
