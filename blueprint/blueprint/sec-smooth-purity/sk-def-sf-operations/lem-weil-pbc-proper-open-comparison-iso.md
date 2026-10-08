+++
id = "lem-weil-pbc-proper-open-comparison-iso"
kind = "lemma"
title = "Proper pushforward of extension by zero"
order = 1482
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-weil-pbc-extension-by-zero", "def-weil-pbc-proper-open-comparison", "lem-weil-pbc-proper-open-identification", "lem-weil-pbc-proper-open-section", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
For every datum in
the comparison-map
construction, the specified map $\alpha_{u,K}$ is an isomorphism.

## Proof

On the open $j_2(X)$, the section described in
[lem-weil-pbc-proper-open-section] exhibits $X$ as an open and
closed subscheme of the relevant inverse image, and the comparison
isomorphism $\theta_{u,K}$ of
[lem-weil-pbc-proper-open-identification] is built from the
identity of $K$ on that component; hence $\alpha_{u,K}$ of
[def-weil-pbc-proper-open-comparison], being the adjoint of
$\theta_{u,K}^{-1}$, restricts to the identity of $K$. In
particular this holds at every geometric point of that open, including
points over generic points.

Let $\bar z:\operatorname{Spec}\Omega\to T_2$ instead lie outside
$j_2(X)$, and write $i:T_{1,\bar z}\to T_1$ for the geometric
fibre. The fibre has empty intersection with $j_1(X)$, since
$u j_1=j_2$. Extension by zero in
[def-weil-pbc-extension-by-zero] therefore gives
$i^{-1}j_{1!}K=0$, degree by degree. The geometric-fibre formula
[cor-weil-pbc-geometric-fiber-finite] gives

$$
(Ru_*j_{1!}K)_{\bar z}
\simeq R\Gamma(T_{1,\bar z},i^{-1}j_{1!}K)=0.
$$

The source $j_{2!}K$ also has zero stalk there. Thus the map is a
quasi-isomorphism on every geometric stalk.
[lemma-weil-pbc-geometric-stalk-conservative], applied to the
cohomology sheaves of its cone, proves the assertion.
