+++
id = "lem-fin-coefficients-forgetful-direct-image"
kind = "lemma"
title = "Changing finite coefficient rings in a direct image"
order = 1639
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image"]
+++
Let $\ell$ be a prime, let $A$ be a finite $\mathbf F_\ell$-algebra,
and let $f:X\to Y$ be a morphism of schemes. Forgetting the
$A$-action on an $A$-sheaf identifies its derived direct image with
the derived direct image of the
underlying $\mathbf F_\ell$-sheaf, together with its induced
$A$-action. In particular a sheaf annihilated by a prime $\ell$ can
be computed using $\mathbf F_\ell$-coefficients.
The notation refers to ordinary derived categories.

## Proof

Let $U:\Mod(X,A)\to\Mod(X,\mathbf F_\ell)$ be the forgetful functor,
the restriction of scalars along the ring map
$\mathbf F_\ell\to A$, and let $U_Y$ be its counterpart on $Y$.

*Step 1: $U$ is exact and commutes with the direct image.*
Exactness is read off on underlying sheaves of abelian groups, the
forgetful functor adding and removing no structure. On sections, both
composites $U_Yf_*$ and $f_*U$ send an $A$-sheaf $F$ to the
$\mathbf F_\ell$-module of sections of $F$ over $V\times_YX$ for an
etale $V\to Y$, with the $A$-action forgotten, by the definition of
the direct image in [def-weil-pbc-direct-image]; so the two
functors are equal, not merely isomorphic.

*Step 2: $U$ carries injective $A$-sheaves to injective
$\mathbf F_\ell$-sheaves.* The left adjoint of $U$ is
$-\otimes_{\mathbf F_\ell}A$. This functor is exact: $A$ is a finite
module over the field $\mathbf F_\ell$, hence free, hence flat, and
tensoring with a flat module is exact. A functor whose left adjoint is
exact preserves injective objects, because the adjunction isomorphism
$\operatorname{Hom}(-,\,UJ)\cong\operatorname{Hom}(-\otimes_{\mathbf F_\ell}A,\,J)$ exhibits exactness of the first functor in the first
variable as exactness of the second.

*Step 3: the derived identification.* Let $F\to I^\bullet$ be an
injective resolution of an $A$-sheaf $F$ in the abelian category of
[def-weil-pbc-derived-categories]. The image $UI^\bullet$ is a
complex of injective $\mathbf F_\ell$-sheaves by Step 2; it is exact in
negative degrees and has $H^0=UF$, because $U$ is exact by Step 1 and
commutes with the differentials. Each term of $UI^\bullet$ is
therefore acyclic for $f_*$ over $\mathbf F_\ell$, injective sheaves
being acyclic for a left exact functor. Hence the complex
$f_*(UI^\bullet)$ computes $Rf_*(UF)$; by Step 1 it is the complex
$U_Yf_*(I^\bullet)$, and $f_*(I^\bullet)$ computes $Rf_*F$ over
$A$. The identification is the identity on underlying complexes, so it
is natural in $F$ and $A$-linear, the resolutions being chosen
$A$-linearly.

*Step 4: complexes.* For a bounded-below complex $K$ of
$A$-sheaves one applies Step 3 to a K-injective representative, whose
underlying complex of $\mathbf F_\ell$-sheaves remains acyclic for the
same reason in each degree; unbounded complexes are handled by the same
argument with a K-injective representative in the sense of the
conventions of [def-weil-pbc-derived-categories]. The induced
$A$-actions are those carried by the resolutions, which are $A$-linear
by construction, and the identification is compatible with the
differentials because it is the identity on underlying complexes.
