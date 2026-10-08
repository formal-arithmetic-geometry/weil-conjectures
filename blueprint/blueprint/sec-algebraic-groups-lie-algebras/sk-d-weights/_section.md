+++
id = "sk-d-weights"
kind = "section"
title = "Operations and weight characters"
order = 2535
uses = ["sk-d-linear", "sk-d-monodromy"]
lean = ["Representation.RealCharacter", "Representation.detCharacter", "Representation.HasFiniteGeometricDet", "Representation.detWeight"]
+++
*Definition (sketch).*

Representations of the same degree datum have
diagonal tensor action and the induced action on exterior powers.
For rank $r$, the determinant representation is $\bigwedge^r V$;
write $\delta_V(w)=\det(\rho_V(w))$ for its character.
A real weight character is a homomorphism
$\lambda:k^\times\to(\mathbf R,+)$, so
$\lambda(ab)=\lambda(a)+\lambda(b)$.
A nonzero representation $Q$ has finite geometric determinant if
$\delta_Q(P)$ is finite. Define its determinant weight by

$$
\dw_\lambda(Q)=\frac{\lambda(\delta_Q(\gamma))}{\dim Q}.
$$

For a composition series, constituent weights
mean the weights of its simple quotients. For a chosen simple
decomposition $V=\bigoplus_j V_j$, the rank-counted list repeats
$\dw_\lambda(V_j)$ exactly $\dim V_j$ times.

Uses: [sk-d-linear], [sk-d-monodromy]
