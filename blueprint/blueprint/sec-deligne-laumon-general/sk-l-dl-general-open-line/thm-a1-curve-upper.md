+++
id = "thm-a1-curve-upper"
kind = "theorem"
title = "Compact-support upper bound on a curve"
order = 2828
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "prop-a1-middle-extension-curve-upper"]
+++
Let $C_0$ be a smooth geometrically connected curve and let
$\mathcal F$ be a lisse Weil sheaf that is punctually $\iota$-pure of
weight $w$. Then every $H_c^r(C,\mathcal F)$ has weights at most
$w+r$.

## Proof

Apply [prop-a1-middle-extension-curve-upper] to the identity open
immersion $C_0\hookrightarrow C_0$; its middle extension is
$\mathcal F$ itself, giving the bound $H_c^r(C,\mathcal F)\leq w+r$.
