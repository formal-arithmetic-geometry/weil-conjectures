+++
id = "lem-fin-projective-flat-coherent-ranks"
kind = "lemma"
title = "Constructible dimensions from coherent base change"
order = 1609
uses = ["cor-pc-projective-noetherian-rf-perfect-base-change", "def-pc-morphism-conventions", "def-pc-perfect-complex", "def-pc-projective-morphism", "def-weil-pbc-scheme-conventions", "lem-pc-projective-noetherian-rf-perfect", "pqf-def-coherent", "pqf-def-cohomology"]
+++
Let $f:X\to S$ be a
projective morphism with
Noetherian base and let
$\mathcal G$ be a coherent module
flat over $S$.
For each $r\geq0$, the function
$s\mapsto\dim_{\kappa(\bar s)} H^r(X_{\bar s},\mathcal G_{\bar s})$, with
coherent cohomology, is constructible.

## Proof

By [lem-pc-projective-noetherian-rf-perfect], locally on a
finite affine cover of $S$, the coherent derived direct image is
represented by a bounded complex $C^\bullet$ of finite projective
modules. A further finite open cover makes its finitely many terms
free, by [def-pc-perfect-complex].
By [cor-pc-projective-noetherian-rf-perfect-base-change],
$C^\bullet\otimes\kappa(\bar s)$ computes the displayed fibre
cohomology. If $c_r$ is the rank of $C^r$ on this open, then

$$
h^r(\bar s)=c_r-\operatorname{rank}(d^{r-1}_{\bar s})
-\operatorname{rank}(d^r_{\bar s}).
$$

A matrix has rank exactly $t$ where all its $(t+1)$-minors
vanish and at least one $t$-minor is nonzero; rank zero is defined
by vanishing of all entries. These are finite unions of locally
closed subsets, and there are only finitely many possible ranks.
Intersect the partitions for the two matrices to obtain a finite
locally closed partition on which $h^r$ is constant. Refine the
finitely many base-open partitions to a partition of $S$.
Thus constructibility has been obtained from explicit matrices.
It does not use etale direct-image finiteness.
