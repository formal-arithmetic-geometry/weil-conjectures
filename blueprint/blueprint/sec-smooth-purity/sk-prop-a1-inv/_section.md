+++
id = "sk-prop-a1-inv"
kind = "section"
title = "Weak $\\Aaf^1$-invariance"
order = 1954
uses = ["sk-def-purity-conv"]
lean = ["AlgebraicGeometry.Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf", "AlgebraicGeometry.Etale.injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf", "AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq"]
+++
*Proposition (sketch).*

In the conventions of [sk-def-purity-conv] write $a:\Aaf^1_Y\to Y$ and
$j:\mathbf G_{m,Y}\hookrightarrow\Aaf^1_Y$, and let $i_0,i_1:Y\to\Aaf^1_Y$ be
the sections $t=0$ and $t=1$.

- **(i)** *Uniqueness for lisse sheaf maps.* If $L,M$ are finite
locally constant $\Lambda$-sheaves on $\Aaf^1_Y$, two morphisms $L\to M$
agreeing after $j^*$ agree everywhere. Likewise two morphisms between
finite locally constant sheaves on $\mathbf G_{m,Y}$ agree as soon as they
agree after restriction along the section $i_1$.
- **(ii)** *Invariance along the line.* Let
$F\in D^b_{ctf}(\Aaf^1_Y,\Lambda)$ be, étale-locally on $Y$, a shift and
twist of a finite locally constant rank-one sheaf, and let
$C\in D^b_{ctf}(Y,\Lambda)$. Then local isomorphisms
$F|_{\Aaf^1_{Y_\alpha}}\simeq a^*C|_{Y_\alpha}$ normalized at $t=1$ glue to
a unique isomorphism $F\simeq a^*C$, and restriction along $i_0$ and $i_1$
gives a canonical identification $i_0^*F\simeq C\simeq i_1^*F$.

Such an invariant is therefore *constant* along the $\Aaf^1$-direction:
its values at $t=0$ and $t=1$ agree.

## Proof

(i) $\mathcal Hom(L,M)$ is again finite locally constant, and a section of a
locally constant sheaf on a connected scheme is determined by a single
geometric stalk. Every connected component of $\Aaf^1_Y$ meets
$\mathbf G_{m,Y}$; and $\mathbf G_{m,Y}\to Y$ has geometrically connected
fibres, so every connected component of $\mathbf G_{m,Y}$ meets the section
$i_1$. Apply this to the difference of the two morphisms. Note that this is
ordinary faithfulness for morphisms of *sheaves*; the corresponding
statement for morphisms in the derived category is false, which is why (ii)
is arranged so that what gets glued are sheaf maps.

(ii) After removing the common shift and twist the local comparisons are
morphisms of finite locally constant rank-one sheaves. On an overlap
$Y_{\alpha\beta}$ the two are normalized at $t=1$, so by the second assertion
of (i) they agree on $\mathbf G_{m,Y_{\alpha\beta}}$, and then by the first
assertion they agree on all of $\Aaf^1_{Y_{\alpha\beta}}$. The ordinary
sheaf axiom glues them to a global isomorphism $F\simeq a^*C$, unique again
by (i). Restricting along $i_0$ and $i_1$ gives the two identifications,
hence the constancy.

Uses: [sk-def-purity-conv]
