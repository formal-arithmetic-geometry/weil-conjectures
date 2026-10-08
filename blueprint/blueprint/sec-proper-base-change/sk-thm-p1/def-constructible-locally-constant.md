+++
id = "def-constructible-locally-constant"
kind = "definition"
title = "Locally constant sheaves"
order = 1155
lean = ["AlgebraicGeometry.Scheme.IsLocallyConstantSheaf", "AlgebraicGeometry.Scheme.LocallyConstantDatum"]
uses = ["def-constructible-constant"]
+++
A *trivialising datum* for $\mathcal F\in\shv{\et X}$ is an étale
cover $(U_i\to X)_{i\in I}$ — a jointly surjective family of étale
morphisms — such that for every $i$ the restriction of $\mathcal F$ to
$\et{U_i}$, that is, the sheaf induced by $\mathcal F$ on the site
$\et X$ localised at $U_i$, is constant. The sheaf $\mathcal F$ is
*locally constant* if a trivialising datum exists.
