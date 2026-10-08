+++
id = "d-weights"
kind = "definition"
title = "Operations and weight characters"
order = 2537
uses = ["d-monodromy", "def-mg-determinant-line", "def-mg-weil-composition-series"]
lean = ["Representation.RealCharacter", "Representation.detCharacter", "Representation.HasFiniteGeometricDet", "Representation.detWeight"]
+++
Representations of the same degree datum ([d-monodromy]) have
diagonal tensor action and the induced action on exterior powers.
For rank $r$, the determinant representation is $\bigwedge^r V$
([def-mg-determinant-line]);
write $\delta_V(w)=\det(\rho_V(w))$ for its character.
A real weight character is a homomorphism
$\lambda:k^\times\to(\mathbf R,+)$, so
$\lambda(ab)=\lambda(a)+\lambda(b)$.
A nonzero representation $Q$ has finite geometric determinant if
$\delta_Q(P)$ is finite. Define its determinant weight by

$$
\dw_\lambda(Q)=\frac{\lambda(\delta_Q(\gamma))}{\dim Q}.
$$

For a composition series ([def-mg-weil-composition-series]), constituent weights
mean the weights of its simple quotients. For a chosen simple
decomposition $V=\bigoplus_j V_j$, the rank-counted list repeats
$\dw_\lambda(V_j)$ exactly $\dim V_j$ times.

For $k=\overline{\mathbf Q}_\ell$, an embedding
$\iota:k\hookrightarrow\mathbf C$ and $q>1$, the usual normalization is
$\lambda_\iota(a)=2\log|\iota(a)|/\log q$.
