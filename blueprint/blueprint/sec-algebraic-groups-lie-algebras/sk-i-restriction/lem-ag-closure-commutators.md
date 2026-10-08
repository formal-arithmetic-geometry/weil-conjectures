+++
id = "lem-ag-closure-commutators"
kind = "lemma"
title = "Normality, commutators and the Lie inclusion"
order = 2514
uses = ["d-monodromy", "def-wf-lie-algebra-derivation", "lem-wf-algebraic-component-cosets", "lem-wf-conjugation-geometric-monodromy", "lem-wf-zariski-closure-subgroup"]
+++
For a represented degree datum as in [d-monodromy], $H$ is normal in
$G$, and

$$
aba^{-1}b^{-1}\in H\quad(a,b\in G),\qquad
[\operatorname{Lie}(G^\circ),\operatorname{Lie}(G^\circ)]\subseteq\operatorname{Lie}(H^\circ).
$$

## Proof

*Normality and commutators.* The kernel $P$ of the degree map in
[d-monodromy] is normal, so conjugation by an element of $\rho(W)$
preserves $\rho(P)$ and, being a homeomorphism, preserves its closure $H$
(as in [lem-wf-conjugation-geometric-monodromy]; both closures are
groups by [lem-wf-zariski-closure-subgroup]).
For fixed $h\in H$ the condition $ghg^{-1}\in H$ is closed in $G$ and
contains $\rho(W)$, hence contains $G$; applying it to $g^{-1}$ gives
$gHg^{-1}=H$. Since $\mathbf Z$ is abelian the degree map kills
commutators, so commutators of elements of $\rho(W)$ lie in $H$. Fixing
one variable, $a\mapsto aba^{-1}b^{-1}$ is regular, so the preimage of $H$
is closed and contains $\rho(W)$, hence $G$; fixing $a\in G$ and repeating
in the other variable gives the assertion on all of $G\times G$. No
quotient algebraic group is needed.

*The Lie inclusion.* Fix $a\in G$. The morphism
$b\mapsto aba^{-1}b^{-1}$ of the reduced variety $G$ sends every
$k$-point into the closed subvariety $H$, so by the vanishing principle
(a function on a reduced affine variety vanishing at every $k$-point is
zero) it factors through $H$. It sends $1$ to $1$; differentiating at
$b=1$ in the dual-number description of
[def-wf-lie-algebra-derivation] gives

$$
(\operatorname{Ad}(a)-1)\operatorname{Lie}(G)\subseteq\operatorname{Lie}(H).
$$

Now fix $X\in\operatorname{Lie}(G)$. The morphism
$a\mapsto(\operatorname{Ad}(a)-1)X$ from $G$ to the vector space
$\operatorname{Lie}(G)$ sends every $k$-point into the linear subspace
$\operatorname{Lie}(H)$, so again it factors through it. Its differential
at $a=1$ along $Y\in\operatorname{Lie}(G)$ is $[Y,X]$, since
$(1+\varepsilon Y)X(1-\varepsilon Y)-X=\varepsilon[Y,X]$. Hence
$[Y,X]\in\operatorname{Lie}(H)$. Finally, the identity components are
open by [lem-wf-algebraic-component-cosets], so
$\operatorname{Lie}(G^\circ)=\operatorname{Lie}(G)$ and
$\operatorname{Lie}(H^\circ)=\operatorname{Lie}(H)$. Spanning over all
such brackets gives the inclusion.
