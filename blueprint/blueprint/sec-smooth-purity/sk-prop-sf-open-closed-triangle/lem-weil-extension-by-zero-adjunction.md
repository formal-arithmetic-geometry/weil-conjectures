+++
id = "lem-weil-extension-by-zero-adjunction"
kind = "lemma"
title = "Adjunction for extension by zero"
order = 1835
uses = ["def-weil-extension-by-zero", "def-weil-pbc-proetale-site"]
+++
The functor $j_!$ of [def-weil-extension-by-zero] is left adjoint to
restriction $j^*$ on pro-etale module sheaves.

## Proof

For an open immersion the site over $U$ is the slice of
[def-weil-pbc-proetale-site] over $U$: maps into $U$ are unique
when they exist, and the coverings are the same coverings over the larger
scheme. A morphism from the presheaf $P_M$ of [def-weil-extension-by-zero] to
a sheaf $N$ is therefore precisely a compatible family $M(V)\to N(V)$ on
objects over $U$; on all other objects the source is zero. This is a morphism
$M\to j^*N$. Sheafification preserves maps to sheaves, so it gives
$\operatorname{Hom}(j_!M,N)=\operatorname{Hom}(M,j^*N)$, naturally in both
arguments.
