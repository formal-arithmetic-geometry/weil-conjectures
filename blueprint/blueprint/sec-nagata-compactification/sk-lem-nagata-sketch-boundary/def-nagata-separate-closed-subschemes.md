+++
id = "def-nagata-separate-closed-subschemes"
kind = "definition"
title = "Closed-boundary separation blow-up"
order = 247
lean = ["AlgebraicGeometry.separationBlowup"]
uses = ["def-nagata-admissible-blowup", "def-nagata-global-blowup", "def-nagata-strict-transform", "lemma-nagata-separate-closed-data-exists"]
+++
Under the hypotheses of
[lemma-nagata-separate-closed-data-exists], choose its center
$C\hookrightarrow Z$. Compose it with the finite-presentation closed
immersion $Z\hookrightarrow X$, and define
$\mathsf{SepBl}_U(Z_1,Z_2)\to X$ to be the blow-up of $X$ along the
resulting center $C\hookrightarrow Z\hookrightarrow X$.
