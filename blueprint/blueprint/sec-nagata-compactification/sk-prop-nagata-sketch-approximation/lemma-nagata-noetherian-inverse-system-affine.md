+++
id = "lemma-nagata-noetherian-inverse-system-affine"
kind = "lemma"
title = "Noetherian approximation of an affine scheme"
order = 343
lean = ["AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine"]
uses = ["def-nagata-noetherian-inverse-system", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-ring-finite-type-subalgebras"]
+++
Let $S=\operatorname{Spec}(A)$ be an affine scheme. Order the finitely
generated $\mathbf Z$-subalgebras $A_0\subseteq A$ by inclusion. Then the
spectra $\operatorname{Spec}(A_0)$ form a cofiltered system of schemes of
finite type over $\mathbf Z$ with affine transition morphisms, and $S$ is
its inverse limit.

## Proof

Finitely generated $\mathbf Z$-subalgebras are directed by
[lemma-nagata-ring-finite-type-subalgebras], and each
$\operatorname{Spec}(A_0)$ is of finite type over $\mathbf Z$, hence
Noetherian by the Hilbert basis theorem. Every transition morphism is
$\operatorname{Spec}$ of a ring map and therefore affine. By the same
lemma, $A$ is the filtered colimit of the $A_0$; since $\operatorname{Spec}$
is a right adjoint it takes this colimit of rings to a limit of schemes, so
$S=\varprojlim\operatorname{Spec}(A_0)$.
