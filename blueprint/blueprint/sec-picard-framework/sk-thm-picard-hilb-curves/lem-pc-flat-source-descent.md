+++
id = "lem-pc-flat-source-descent"
kind = "lemma"
title = "Flatness descends along a flat surjection on the source"
order = 789
uses = ["def-pc-morphism-conventions"]
+++
Let $X'\xrightarrow{u}X\xrightarrow{f}S$ be morphisms of schemes.
If $u$ is surjective and flat,
and $f\circ u$ is flat, then $f$ is flat.

## Proof

For $x\in X$, choose $x'\in X'$ above it and put $s=f(x)$.
The local ring map $\mathcal O_{X,x}\to\mathcal O_{X',x'}$ is flat
and local, hence faithfully flat. To check flatness of
$\mathcal O_{X,x}$ over $\mathcal O_{S,s}$, tensor an injection of
$\mathcal O_{S,s}$-modules first with $\mathcal O_{X,x}$ and then
with $\mathcal O_{X',x'}$. The composite is injective since
$\mathcal O_{X',x'}$ is flat over $\mathcal O_{S,s}$; faithful flatness
therefore makes the first tensor map injective. This proves
flatness at every $x$.
