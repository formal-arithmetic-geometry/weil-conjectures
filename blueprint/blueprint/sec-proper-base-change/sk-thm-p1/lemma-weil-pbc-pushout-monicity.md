+++
id = "lemma-weil-pbc-pushout-monicity"
kind = "lemma"
title = "Pushout preserves monomorphisms"
order = 1122
+++
Given monomorphisms $A\hookrightarrow B$ and $A\hookrightarrow C$ of sheaves,
the canonical map $C\to B\amalg_A C$ is monic.

## Proof

Let $P=B\amalg_A C$ be the pushout in sheaves. It is the cokernel sheaf of
$A\to B\oplus C$, $a\mapsto(i_Ba,-i_Ca)$. If $c\in C(V)$ maps to zero in
$P(V)$, then by the definition of a sheaf cokernel there is an etale cover
$\{V_\alpha\to V\}$ and $a_\alpha\in A(V_\alpha)$ with
$i_C(a_\alpha)=c|_{V_\alpha}$ and $i_B(a_\alpha)=0$. Since $i_B$ is monic,
$a_\alpha=0$, hence $c|_{V_\alpha}=0$. The sheaf axiom gives $c=0$.
This proves monicity on arbitrary etale objects, and the same local
equalizer calculation proves naturality of the pushout map.
