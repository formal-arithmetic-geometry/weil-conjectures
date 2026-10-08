+++
id = "prop-exc-open-adjoint"
kind = "theorem"
title = "The right adjoint for an open immersion"
order = 1853
tags = ["latex:proposition"]
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-extension-by-zero", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-weil-extension-by-zero-adjunction", "lem-weil-extension-by-zero-exact"]
+++
Let $A$ be a finite commutative ring, including the
finite coefficient rings
$A_{E,n}$,
and let $j:U\hookrightarrow X$ be a
open immersion.
On the small pro-etale sites,
extension by zero has the
inverse image as its
right adjoint on the entire ordinary derived categories:

$$
j_!:D(U_{\mathrm{proet}},A)\rightleftarrows
D(X_{\mathrm{proet}},A):j^*.
$$

In particular, the right adjoint is constructed without a constructibility
or finite-Tor hypothesis.

## Proof

The site over the open $U$ is the localization of the site of
[def-weil-pbc-proetale-site] at the subterminal sheaf represented by
$U$. Thus restriction $j^*$ is exact. For module sheaves $M,N$,
the extension-by-zero adjunction of
[lem-weil-extension-by-zero-adjunction] gives

$$
\operatorname{Hom}(j_!M,N)=\operatorname{Hom}(M,j^*N).
$$

Exactness of extension by zero is proved using presheaf kernels,
local lifting, and sheafification in
[lem-weil-extension-by-zero-exact]. Apply the two exact
functors degree by degree to complexes.
They preserve acyclic complexes. Their sheaf-level unit and counit are
chain maps, still satisfy both triangular identities, and descend through
localization at quasi-isomorphisms. Hence they define the asserted
adjunction, with inverse image as in
[def-weil-derived-pullback-tensor-hom].
