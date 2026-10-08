+++
id = "sk-p-dl-a1-correction"
kind = "section"
title = "The zero-extension comparison"
order = 2767
uses = ["sk-p-dl-a1-middle", "sk-p-dl-a1-perverse", "sk-p-real-semi"]
lean = ["AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.isLisse", "AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection.hasWeightsAtMost"]
+++
*Proposition (sketch).*

For nonexceptional $M$ pure of weight $w$, put
$B=j_*M/j_!M$. There are ordinary sheaves $G$ and $B'$ such that

$$
\begin{gathered}
\DLAFT_\psi(j_!M[1])\simeq G[1],\qquad
\DLAFT_\psi(B)\simeq B'[1],\\
0\longrightarrow B'\longrightarrow G\longrightarrow j'_*M'
\longrightarrow0.
\end{gathered}
$$

The correction $B'$ is lisse on the entire dual line, with weights at
most $w$.

## Proof

Rotate the triangle of $0\to j_!M\to j_*M\to B\to0$ to
$B\to j_!M[1]\to j_*M[1]\to B[1]$. Its first three terms form a short
exact sequence of curve perverse sheaves. Apply perverse Fourier
exactness. Each punctual summand of $B$ transforms into a lisse
Artin–Schreier kernel with its coefficient module, shifted by one;
the middle-extension transform is $(j'_*M')[1]$. Ordinary cohomology
gives the asserted concentration and exact sequence.

At a boundary point $s$, $B_{\bar s}=(j_*M)_{\bar s}$ has weights at
most $w$ by semicontinuity. The Artin–Schreier kernel has weight zero.
For nonrational $s$, Frobenius permutes its geometric summands; taking
a power around a permutation cycle gives the same normalized weight
bound. Thus every summand, and hence $B'$, has weights at most $w$.

Uses: [sk-p-dl-a1-middle], [sk-p-dl-a1-perverse], [sk-p-real-semi]
