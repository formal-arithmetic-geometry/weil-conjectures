+++
id = "lem-weil-pbc-basis-derived-detection"
kind = "lemma"
title = "Derived sections on the basis detect isomorphisms"
order = 1288
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-ind-etale-basis", "lem-weil-pbc-ind-etale-basis", "lem-weil-pbc-proetale-restriction-injectives"]
+++
Let $X$ be affine. A morphism between bounded-below complexes of pro-etale
module sheaves is an isomorphism if its derived sections on every
$W\in\mathcal B_X$ are isomorphisms.

## Proof

Take the cone in the ordinary derived category and represent it by a
bounded-below injective complex $J^\bullet$. By
[lem-weil-pbc-proetale-restriction-injectives], $\Gamma(W,J^\bullet)$
computes its derived sections on $W$. Its cohomology sheaf in degree $n$ is
the sheafification of the presheaf $W\mapsto H^n\Gamma(W,J^\bullet)$: kernels
are computed objectwise, and cokernels are then sheafified. All these groups
are zero on the basis by hypothesis, so [lem-weil-pbc-ind-etale-basis] makes
every cohomology sheaf zero. The cone is zero and the morphism is an
isomorphism.
