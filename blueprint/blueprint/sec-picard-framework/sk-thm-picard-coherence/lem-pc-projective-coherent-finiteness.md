+++
id = "lem-pc-projective-coherent-finiteness"
kind = "lemma"
title = "Coherent cohomology of a projective scheme over a Noetherian ring"
order = 656
uses = ["def-pc-projective-morphism", "def-pc-projective-space-twist", "lem-pc-closed-immersion-coherent-cohomology", "lem-pc-projective-space-coherent-finiteness", "lem-pc-projective-space-cohomology-bound", "pqf-def-coherent", "pqf-def-cohomology"]
+++
Let $A$ be Noetherian, let $f:X\to\operatorname{Spec}(A)$ be
projective, and let
$\mathcal F$ be a coherent module.
Then $H^q(X,\mathcal F)$ is a finite $A$-module for every $q$.
For an embedding $X\hookrightarrow\mathbf P^n_A$, these groups
vanish for $q>n$.

## Proof

Take a closed immersion $i:X\hookrightarrow\mathbf P^n_A$ from
[def-pc-projective-morphism]. Its affine charts are finite
type over the Noetherian ring $A$, so $X$ is locally Noetherian.
By [lem-pc-closed-immersion-coherent-cohomology],
$i_*\mathcal F$ is coherent and has the same cohomology as
$\mathcal F$. Apply
[lem-pc-projective-space-coherent-finiteness], [lem-pc-projective-space-cohomology-bound]
to $i_*\mathcal F$ on $\mathbf P^n_A$.
