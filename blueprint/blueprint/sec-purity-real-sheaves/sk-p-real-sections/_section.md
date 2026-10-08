+++
id = "sk-p-real-sections"
kind = "section"
title = "Global sections as invariants"
order = 2593
uses = ["sec-algebraic-groups-lie-algebras", "sk-d-real-operations", "sk-d-real-weil", "sk-i-real-sheaves"]
lean = ["AlgebraicGeometry.WeilGroup.globalSections_eq_invariants", "AlgebraicGeometry.WeilGroup.globalSections"]
+++
*Proposition (sketch).*

Keep the notation of [sk-i-real-sheaves]. Let $U_0\subseteq C_0$ be a
nonempty open subscheme, $U=U_0\times_{\Fq}k$ its base change and $\pi_1(U)$
its geometric fundamental group; restriction gives the Weil group $W(U_0)$
with geometric subgroup $\pi_1(U)$. For a subgroup $I$ write
$V^{I}=\{v\in V:gv=v\text{ for all }g\in I\}$ for the invariants, as in
[sk-d-real-operations], and let $H^0$ denote ordinary etale global
sections. Then

$$
H^0\bigl(U,\mathcal F|_{U}\bigr)=V^{\pi_1(U)},
$$

compatibly with the residual action of $F=\rho(\gamma)$ on both sides.

## Proof

Apply [sk-i-real-sheaves] on the connected $U$. A global section of
$\mathcal F|_{U}$ is a morphism from the constant rank-one sheaf, hence under
the equivalence a map of $\pi_1(U)$-representations from the trivial line to
$V$. Such a map is determined by the image of $1$, which must be fixed by
every element; conversely every fixed vector defines one. This gives
$H^0(U,\mathcal F|_{U})=V^{\pi_1(U)}$. The subgroup $\pi_1(U)$ is normal in
$W(U_0)$, so the degree-one lift normalizes its action and therefore preserves
the invariants; the identification is equivariant for the residual $F$.

Uses: [sk-d-real-operations], [sk-d-real-weil], [sk-i-real-sheaves]
