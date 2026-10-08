+++
id = "prop-pod-biduality-at-the-point"
kind = "theorem"
title = "Biduality at the point"
order = 2415
tags = ["latex:proposition"]
uses = ["def-pod-conventions", "def-pod-perfect-point-complex", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-coefficient-point", "def-weil-geometric-hypotheses", "lem-pod-finite-projective-tensor-hom"]
+++
In the Poincare duality conventions of this chapter (the fixed setting),
let $C$ be a perfect point complex. The
evaluation and coevaluation give a canonical isomorphism

$$
C\xrightarrow{\ \sim\ }C^{\vee\vee},
$$

and for every object $D$ of the category at the point, the canonical
tensor–internal-Hom comparison

$$
C^\vee\otimes_A^LD\xrightarrow{\ \sim\ }R\operatorname{Hom}_A(C,D)
$$

is an isomorphism.

## Proof

An object of the category at the point of
[def-weil-finite-coefficient-point] is a complex of $A$-modules.
Step 1: for $P$ a single finite projective
$A$-module concentrated in degree zero, the canonical map
$P^\vee\otimes_A^LD\to\operatorname{Hom}_A(P,D)$ is an isomorphism
because $\operatorname{Hom}_A(P,-)$ is exact, so
$R\operatorname{Hom}_A(P,D)$ is represented by the termwise Hom
complex, and the map is the one of
[lem-pod-finite-projective-tensor-hom] at the base $s$, an
isomorphism since $P$ is dualizable; and $P\to P^{\vee\vee}$ is the
iso of a finite projective module with its double dual. Step 2: for a
bounded complex $P^\bullet$ of finite projective modules in a finite
range $[a,b]$, the two statements are proved by descending induction
on the number of nonzero terms: for the cone
$\operatorname{cone}(P^{b-1}\to P^b)$-decomposition, or, directly, by
writing $P^\bullet$ as the finite iterated cone of the truncation
triangles $\tau^{\leq i-1}P^\bullet\to\tau^{\leq i}P^\bullet\to P^i[-i]\xrightarrow{+1}$, and using that
$C\mapsto R\operatorname{Hom}_A(C,D)$ and $C\mapsto C^\vee\otimes_A^LD$
convert distinguished triangles to distinguished triangles (in the
argument, together with the naturality of the canonical map) and the
five lemma. Step 3: the general $C$ is quasi-isomorphic to such a
$P^\bullet$ by [def-pod-perfect-point-complex]; replacing $C$
by $P^\bullet$ is legitimate because both sides are quasi-isomorphism
invariants: the derived functors of
[def-weil-derived-pullback-tensor-hom] are independent of the
selected resolutions. The canonicality of both isomorphisms is the
naturality of the adjunction in $C$ and $D$.
