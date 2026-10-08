+++
id = "sk-p-dl-a1-exact"
kind = "section"
title = "Exactness at a fixed pure weight"
order = 2783
uses = ["sk-d-dl-a1-setup", "sk-i-dl-a1-local", "sk-p-real-semi"]
lean = ["AlgebraicGeometry.shortExact_map_directImage"]
+++
*Proposition (sketch).*

For a short exact sequence $0\to F_1\to F\to F_2\to0$ of lisse
Weil sheaves, all pure of the same weight $w$, ordinary middle
extension is exact:

$$
0\longrightarrow j_*F_1\longrightarrow j_*F
\longrightarrow j_*F_2\longrightarrow0.
$$

## Proof

The possible failure of surjectivity is the connecting map
$\delta:j_*F_2\to R^1j_*F_1$, which vanishes on the open.
At a missing point the source has weights at most $w$ by
semicontinuity. The dual $F_1^\vee$ has weight $-w$, so its
middle-extension stalk has weights at most $-w$. Local duality
identifies $(R^1j_*F_1)_{\bar s}$ with the dual of that stalk,
twisted by $(-1)$; its weights are at least $w+2$.
A Frobenius-equivariant map across this strict weight gap is zero:
its image would have to satisfy both incompatible bounds.
Thus $\delta$ vanishes on every geometric stalk, proving exactness.

Uses: [sk-d-dl-a1-setup], [sk-i-dl-a1-local], [sk-p-real-semi]
