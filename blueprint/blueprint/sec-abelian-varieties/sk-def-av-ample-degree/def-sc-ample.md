+++
id = "def-sc-ample"
kind = "definition"
title = "Very ample and ample line bundles"
lean = ["AlgebraicGeometry.IsAmple"]
order = 436
+++
Let $X$ be a proper scheme over $k$ and $\mathcal L$ a line
bundle on $X$. $\mathcal L$ is *very ample* if the complete
linear system $|\mathcal L|=\mathbf P(H^0(X,\mathcal L)^{\vee})$
gives a closed immersion $i:X\hookrightarrow\mathbf P^N_k$ with
$i^*\mathcal O(1)\cong\mathcal L$ (so that every global section of
$\mathcal L$ is pulled back from a linear form on $\mathbf P^N$)
(*reference: Stacks Project, Morphisms of Schemes, Definition
29.39.1, [Tag 01VM](https://stacks.math.columbia.edu/tag/01VM) (very ample) and Properties of Schemes, Section
28.27, [Tag 01PR](https://stacks.math.columbia.edu/tag/01PR) (ample invertible sheaves)*). $\mathcal L$ is
*ample* if
$\mathcal L^{\otimes m}$ is very ample for some $m\geq1$ (the
standard characterization for proper schemes; *reference:
Stacks Project, Properties of Schemes, Proposition 28.27.13, [Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)*).
