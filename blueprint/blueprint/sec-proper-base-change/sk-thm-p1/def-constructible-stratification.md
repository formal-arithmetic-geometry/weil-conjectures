+++
id = "def-constructible-stratification"
kind = "definition"
title = "Stratifications"
order = 1158
lean = ["AlgebraicGeometry.Scheme.Stratification", "Topology.Stratification"]
+++
A *stratification* of a topological space $T$ is a finite family
$(T_k)_{k<n}$ of pairwise disjoint locally closed subsets covering $T$
(Stacks Project, Tag `09XZ`, with finiteness added). A
*stratification* of a scheme $X$ is a stratification $(X_k)_{k<n}$ of
its underlying space together with, for each $k$, a scheme $Z_k$ and an
immersion $\iota_k\colon Z_k\to X$ with set-theoretic image $X_k$.
