+++
id = "sk-prop-jacobian"
kind = "section"
title = "The Jacobian is an abelian variety"
order = 848
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-def-picard-f", "sk-lem-picard-f-open", "sk-lem-picard-zero-dictionary", "sk-prop-picard-degree-decomposition", "sk-prop-picard-jacobian-tangent", "sk-prop-picard-pic-split", "sk-thm-picard-f-representable", "sk-thm-picard-hilb-curves", "sk-thm-picard-rr", "sk-thm-picard-twist"]
lean = ["AlgebraicGeometry.exists_jacobian"]
+++
*Proposition (sketch).*

$\underline{\Pic}^0_{C/k}$ is a proper, smooth, connected, commutative
group scheme of dimension $g$ over $k$, that is, an abelian variety, with
$T_e\underline{\Pic}^0_{C/k}\cong H^1(C,\cO_C)$. Hence
$J(C)=\underline{\Pic}^0_{C/k}$, with its representing isomorphism, is the
Jacobian of [sk-def-av-jacobian], and

$$
\Pic^0(C)=\{\cL\in\Pic(C):\deg\cL=0\}\;\cong\;J(C)(k),
$$

where $\deg\cL=\chi(\cL)-\chi(\cO_C)$, equivalently (by
[sk-thm-picard-rr](RR)) the divisor degree $\deg D$ of any $D$ with
$\cL\cong\cO_C(D)$; and the formation of $J(C)$ commutes with algebraically closed base extension:
$J(C_{k'})=J(C)\times_kk'$ for $k\subseteq k'$ algebraically closed.

## Proof

*Why this is the Jacobian.* By [sk-prop-picard-degree-decomposition]
the subfunctor $\Pic^0_{C/k}$ is represented by the open and closed subgroup
scheme $\underline{\Pic}^0_{C/k}$. A representing object is unique up to
unique isomorphism, so a Jacobian in the sense of [sk-def-av-jacobian]
exists exactly when $\underline{\Pic}^0_{C/k}$ is an abelian variety of
dimension $g$, and then it is $\underline{\Pic}^0_{C/k}$ with its
representing isomorphism. It remains to prove the geometric properties.

By [sk-prop-picard-degree-decomposition], $\underline{\Pic}^0_{C/k}$ is isomorphic to
$\underline{\Pic}^g_{C/k}$ (translation by $\cO_C(gP)$), so it suffices
to prove the geometric properties for $\underline{\Pic}^g_{C/k}$.

*Smooth of dimension $g$.* The subfunctor $F$ of [sk-def-picard-f]
is open ([sk-lem-picard-f-open]), represented by an open
$W\subseteq\underline{\Hilb}^g_{C/k}$ ([sk-thm-picard-f-representable]),
and its classes have degree $g$ ([sk-lem-picard-zero-dictionary]); so
$W$ is an open subscheme $U\subseteq\underline{\Pic}^g_{C/k}$, smooth of
dimension $g$ because $\underline{\Hilb}^g_{C/k}$ is
([sk-thm-picard-hilb-curves] (1)). The translates of $U$ by $k$-points
cover $\underline{\Pic}^g_{C/k}$: for a point $t$ with residue field $K$,
[sk-thm-picard-twist] gives $\cL_0$ on $C$ with
$\cL_0|_{C_K}\otimes\cL_t\in F(K)$, necessarily of degree $0$, so
$t\in\cL_0^{-1}\cdot U$. Hence $\underline{\Pic}^g_{C/k}$ is smooth of
pure dimension $g$; the tangent space is [sk-prop-picard-jacobian-tangent].

*Proper.* The universal divisor of [sk-thm-picard-hilb-curves] (3),
normalized along $P$, defines
$\alpha:\underline{\Hilb}^g_{C/k}\to\underline{\Pic}^g_{C/k}$,
$D\mapsto\cO_C(D)$. It is surjective: over an algebraically closed field
$K$, a class $\cL$ of degree $g$ has $h^0(\cL)\ge\chi(\cL)=1$ by
[sk-thm-picard-rr] (RR), so $\cL\cong\cO_{C_K}(D)$ for the zero divisor
$D$ of a nonzero section, a $K$-point of $\underline{\Hilb}^g_{C/k}$
([sk-thm-picard-hilb-curves] (2)). So $\underline{\Pic}^g_{C/k}$ is
quasi-compact, hence of finite type; it is separated, being a group
scheme over a field whose unit section is a closed immersion; and as the
surjective image of the proper $\underline{\Hilb}^g_{C/k}$ it is proper
(Stacks [`03GN`](https://stacks.math.columbia.edu/tag/03GN)).

*Connected and commutative.* $\underline{\Hilb}^g_{C/k}$ is an
irreducible variety ([sk-thm-picard-hilb-curves] (1)), so its image
$\underline{\Pic}^g_{C/k}$ under $\alpha$ is irreducible. The group law
is the tensor product of invertible modules (Yoneda), which is
commutative.

*Points and base change.* By [sk-prop-picard-pic-split] with
$T=\Spec k$ and $\Pic(\Spec k)=0$, $\underline{\Pic}_{C/k}(k)=\Pic(C)$,
and $J(C)(k)$ is its degree-zero part. The Picard functor, its
normalization along $P$ and the degree commute with base change along
$k\to k'$, so $\underline{\Pic}_{C/k}\times_kk'$ represents
$\Pic_{C_{k'}/k'}$ and its degree-zero part is $J(C_{k'})$.
(Classical: Mumford and Milne, *Abelian Varieties*; Stacks
[`0BA0`](https://stacks.math.columbia.edu/tag/0BA0); the
detailed blueprint node is
`thm-sc-jacobian-representability`.)

Uses: [sk-def-av-jacobian], [sk-def-picard-f], [sk-lem-picard-f-open], [sk-lem-picard-zero-dictionary], [sk-prop-picard-degree-decomposition], [sk-prop-picard-jacobian-tangent], [sk-prop-picard-pic-split], [sk-thm-picard-f-representable], [sk-thm-picard-hilb-curves], [sk-thm-picard-rr], [sk-thm-picard-twist]
