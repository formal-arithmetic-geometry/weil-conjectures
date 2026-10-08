+++
id = "lemma-nagata-projective-space-base-change-proper"
kind = "lemma"
title = "Projective space is proper over its base"
order = 308
lean = ["AlgebraicGeometry.ProjectiveSpace.instIsProper"]
uses = ["def-nagata-affine-proj", "def-nagata-projective-space-base-change"]
+++
For every finite index set $n$ and every scheme $S$, the structural
morphism $\mathbf P(n;S)\to S$ is proper.

## Proof

The polynomial ring $\mathbf Z[T_i:i\in n]$ is of finite type over the
degree-zero part of its total-degree grading, which is $\mathbf Z$, because
$n$ is finite. Hence the verified properness instance for
$\operatorname{Proj}$ of a graded ring of finite type over its degree-zero
part ([def-nagata-affine-proj]) makes
$\mathbf P^n_{\mathbf Z}\to\operatorname{Spec}\mathbf Z$ proper. Since
$\operatorname{Spec}\mathbf Z$ is the terminal scheme, the same holds for
$\mathbf P^n_{\mathbf Z}\to\ast$, and properness is stable under base
change, so the first projection $\mathbf P(n;S)\to S$ is proper.
