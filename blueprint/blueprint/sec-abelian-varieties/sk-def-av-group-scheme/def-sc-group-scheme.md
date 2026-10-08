+++
id = "def-sc-group-scheme"
kind = "definition"
title = "Group schemes over a field"
order = 422
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $k$ be a field. A $k$-*group scheme* is a $k$-scheme
$G$ together with morphisms $m:G\times_kG\to G$ (multiplication),
$i:G\to G$ (inverse) and $e:\operatorname{Spec}k\to G$ (identity)
such that the usual associativity, unit and inverse diagrams
commute; equivalently, the functor of points
$R\mapsto G(R)$ takes values in groups. The group scheme is
*commutative* if $m\circ s=m$, where $s$ swaps the two
factors. A *homomorphism* $f:G\to H$ of group schemes is a
morphism of schemes compatible with the multiplications; the
*kernel* of $f$ is the closed subgroup scheme

$$
\ker f:=G\times_{H,f,e_H}\operatorname{Spec}k.
$$

(That this fibre product is a closed subgroup scheme is
[lem-sc-kernel-subgroup].) The group scheme $G$ is *finite* if its
structure morphism $G\to\operatorname{Spec}k$ is finite in the sense
of [def-weil-pbc-scheme-conventions]; then $G=\operatorname{Spec}A$
with $A=\Gamma(G,\mathcal O_G)$ a finite-dimensional $k$-algebra, and
the *order* of $G$ is

$$
\lvert G\rvert:=\dim_k\Gamma(G,\mathcal O_G).
$$

The group scheme $G$ is *étale* over $k$ if its structure morphism is
étale in the sense of [def-weil-pbc-scheme-conventions]. A finite
$k$-algebra $A$ is a *finite étale $k$-algebra* if it is isomorphic to
a finite product $L_1\times\dots\times L_r$ of finite separable field
extensions $L_j$ of $k$. For finite $G$, the group scheme $G$ is étale
over $k$ if and only if $\Gamma(G,\mathcal O_G)$ is a finite étale
$k$-algebra ([lem-sc-finite-etale-algebra-criterion]).
