+++
id = "sk-prop-nagata-sketch-prepared"
kind = "section"
title = "Prepared sides"
order = 261
uses = ["sk-lem-nagata-sketch-boundary", "sk-lem-nagata-sketch-closure", "sk-lem-nagata-sketch-graph"]
lean = ["AlgebraicGeometry.exists_prepared_twoOpenSide"]
+++
*Proposition (sketch).*

There are scheme-theoretically dense compactifications $U_i\hookrightarrow X_i$, opens
$U_i\subseteq V_i\subseteq X_i$, and proper maps $\psi_i:V_i\to U$
which are the identity over $U_i$. Put, for $\{i,j\}=\{1,2\}$,

$$
Z_i=(U\setminus U_j)_{\mathrm{red}},\qquad
Z_{i,k}=\psi_i^{-1}(Z_k),\qquad
B_{i,k}=\overline{|Z_{i,k}|}^{\,X_i}.
$$

The choices can be made so that $B_{i,1}\cap B_{i,2}=\varnothing$.
Further $V_i$-admissible blow-ups preserve these properties.

## Proof

Refine the two compactifications to scheme-theoretically dense ones
and apply proper graph
extension. The two closed subsets $Z_{i,1},Z_{i,2}$ of $V_i$ are
disjoint and constructible, so separate their closures. A subsequent
$V_i$-admissible blow-up transports the same open and proper map;
the new closures lie in the inverse images of the old disjoint closures.

Uses: [sk-lem-nagata-sketch-boundary], [sk-lem-nagata-sketch-closure], [sk-lem-nagata-sketch-graph]
