+++
id = "sk-prop-picard-jacobian-tangent"
kind = "section"
title = "The tangent space of the Jacobian"
order = 846
uses = ["sk-def-av-jacobian", "sk-def-picard-pic", "sk-lem-picard-cech-computes", "sk-prop-picard-degree-decomposition"]
lean = ["AlgebraicGeometry.nonempty_tangentSpaceAt_equiv_H_one"]
+++
*Proposition (sketch).*

The tangent space of the group scheme $\underline{\Pic}^0_{C/k}$ of
[sk-prop-picard-degree-decomposition] at the unit is
$k$-linearly isomorphic to $H^1(C,\cO_C)$:

$$
T_e\underline{\Pic}^0_{C/k}\cong H^1(C,\cO_C)\qquad(\text{isomorphism of $k$-vector spaces}),
$$

a $k$-vector space of dimension $g$.

## Proof

Let $k[\varepsilon]=k[x]/(x^2)$. The tangent space at $e$ is the set of
$k[\varepsilon]$-points of $\underline{\Pic}^0_{C/k}$ reducing to $e$, that is, by
[sk-def-picard-pic] and the normalization along $P$, the set of
invertible modules on $C_{k[\varepsilon]}$ whose restriction to $C$ is
trivial, up to isomorphism (a degree-$0$ condition that is automatic,
since the degree is locally constant). Fix a finite affine open cover
$\mathfrak U=\{U_i\}$ of $C$. Such a module is trivial on every
$U_i\times_kk[\varepsilon]$ (an invertible module trivial modulo the
nilpotent $\varepsilon$ on an affine scheme is trivial), so it is given
by transition functions in
$\ker\bigl(\cO(U_{ij}\times k[\varepsilon])^\times\to\cO(U_{ij})^\times\bigr) =\{1+\varepsilon g_{ij}\}$. Since
$(1+\varepsilon a)(1+\varepsilon b)=1+\varepsilon(a+b)$, the cocycle
condition reads $g_{ij}+g_{jk}=g_{ik}$, and changing the trivializations
by $1+\varepsilon h_i$ changes $g_{ij}$ by $h_j-h_i$. So
$(1+\varepsilon g_{ij})\mapsto[(g_{ij})]$ is a bijection from the
tangent space onto $\check H^1(\mathfrak U,\cO_C)$.

*The $k$-linear structures.* On the tangent space
$T_e=\ker\bigl(\underline{\Pic}^0_{C/k}(k[\varepsilon])\to\underline{\Pic}^0_{C/k}(k)\bigr)$
the addition is the group law of $\underline{\Pic}^0_{C/k}$ (which agrees
with the addition defined through
$k[\varepsilon]\times_kk[\varepsilon]=k[\varepsilon_1,\varepsilon_2]/(\varepsilon_1,\varepsilon_2)^2$),
and a scalar $\lambda\in k$ acts through the $k$-algebra map
$\sigma_\lambda:k[\varepsilon]\to k[\varepsilon]$, $\varepsilon\mapsto\lambda\varepsilon$,
by $\xi\mapsto\underline{\Pic}^0_{C/k}(\sigma_\lambda)(\xi)$; both
preserve $T_e$ because $\sigma_\lambda$ and the group law commute with
reduction modulo $\varepsilon$. The group law is the tensor product of
invertible modules (Yoneda), whose transition functions multiply:
$(1+\varepsilon a)(1+\varepsilon b)=1+\varepsilon(a+b)$, so the bijection
is additive. Pulling back along $\mathrm{id}_C\times\Spec\sigma_\lambda$
replaces the transition functions $1+\varepsilon g_{ij}$ by
$\sigma_\lambda(1+\varepsilon g_{ij})=1+\varepsilon\lambda g_{ij}$, so the
class $[(g_{ij})]$ goes to $\lambda[(g_{ij})]$. Hence the bijection is
a $k$-linear isomorphism
$T_e\underline{\Pic}^0_{C/k}\cong\check H^1(\mathfrak U,\cO_C)$, and
$\check H^1(\mathfrak U,\cO_C)\cong H^1(C,\cO_C)$ $k$-linearly by
[sk-lem-picard-cech-computes]; its dimension is the genus $g$ by the
conventions.

Uses: [sk-prop-picard-degree-decomposition], [sk-def-picard-pic], [sk-lem-picard-cech-computes]
