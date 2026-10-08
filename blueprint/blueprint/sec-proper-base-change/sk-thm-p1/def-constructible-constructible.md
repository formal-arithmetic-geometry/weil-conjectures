+++
id = "def-constructible-constructible"
kind = "definition"
title = "Constructible sheaves"
order = 1159
lean = ["AlgebraicGeometry.Scheme.IsConstructibleSheaf"]
uses = ["def-constructible-finite-locally-constant", "def-constructible-stratification"]
+++
A sheaf $\mathcal F\in\shv{\et X}$ is *constructible* if there is a
stratification $(\iota_k\colon Z_k\to X)_{k<n}$ of $X$ such that each
pullback $\iota_k^*\mathcal F$ is finite locally constant.
