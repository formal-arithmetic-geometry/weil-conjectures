+++
id = "thm-weil-pbc-weak-etale-refinement"
kind = "theorem"
title = "Ind-etale refinement of a weakly etale map"
order = 1232
uses = ["def-weil-pbc-ind-etale-algebra", "def-weil-pbc-weak-etale-refinement", "lem-weil-pbc-ind-etale-stability", "lem-weil-pbc-local-rings-ind-zariski", "lem-weil-pbc-retained-localization", "lem-weil-pbc-strict-w-cover", "lem-weil-pbc-weak-etale-field", "thm-weil-pbc-weak-etale-strict-local"]
+++
For the construction of [def-weil-pbc-weak-etale-refinement], the map $B\to
B'$ is faithfully flat and ind-etale, and $A\to B'$ is ind-etale.

## Proof

Use $C,J,D_0$ from [def-weil-pbc-weak-etale-refinement]. By
[lem-weil-pbc-strict-w-cover], $C/A$ is faithfully flat and ind-etale, and
its maximal local rings are strictly henselian. The fibres of $D_0/C$ are
algebraic over their base fields by
[lem-weil-pbc-weak-etale-field]. Thus $T=V(JD_0)$ consists of closed points
of $D_0$. [lem-weil-pbc-retained-localization] makes $B'$ w-local with closed
points $T$, unchanged local rings there, and $D_0\to B'$ ind-Zariski.

At every maximal ideal $n\subset B'$, its contraction $m\subset C$ is
maximal. The local map $C_m\to B'_n$ is weakly etale by
[lem-weil-pbc-ind-etale-stability], so is an isomorphism by
[thm-weil-pbc-weak-etale-strict-local]. Every prime of $B'$ lies under a
maximal ideal. Localizing this isomorphism again shows that $C\to B'$
identifies all local rings. It is therefore ind-Zariski by
[lem-weil-pbc-local-rings-ind-zariski]. Composition with $A\to C$ proves that
$A\to B'$ is ind-etale.

The map $B\to D_0$ is ind-etale by base change from $A\to C$; composition
makes $B\to B'$ ind-etale and flat as well. The closed point set $V(J)$
surjects onto $\operatorname{Spec}A$ by
[lem-weil-pbc-strict-w-cover]. Its base change $T$ therefore surjects onto
$\operatorname{Spec}B$, and all these points are retained in
$\operatorname{Spec}B'$. This proves faithful flatness. The construction
gives the refinement theorem commonly formulated in
[Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z); its
covering and local-ring steps have been proved above.
