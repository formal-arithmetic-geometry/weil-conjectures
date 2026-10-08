+++
id = "lem-wf-rank-one-component-modulus"
kind = "lemma"
title = "A rank-one character has constant modulus on a degree component"
order = 2555
uses = ["def-wf-degree-components", "lem-wf-rank-one-algebraic-extension"]
+++
Let $A,c,j_\chi$ be as in
[lem-wf-rank-one-algebraic-extension], and fix an embedding
$\iota:E\hookrightarrow\mathbf C$. If
$z\in G_{\mathrm{arith}}(\chi)^{[m]}$, then

$$
|\iota(j_\chi(z))|=|\iota(c)|^m.
$$

## Proof

By [def-wf-degree-components], write $z=(a,m)$. The description
in [lem-wf-rank-one-algebraic-extension] gives
$j_\chi(z)=ac^m$, where $a\in A$. Every element of the finite
subgroup $A\subset E^\times$ is a root of unity, so
$|\iota(a)|=1$. Taking complex absolute values proves the formula.
