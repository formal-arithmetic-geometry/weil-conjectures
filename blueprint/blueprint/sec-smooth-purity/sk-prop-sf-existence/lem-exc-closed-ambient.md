+++
id = "lem-exc-closed-ambient"
kind = "lemma"
title = "Closed-immersion right adjoint before restriction"
order = 1803
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-etale-site", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $i:Z\hookrightarrow T$ be a
closed immersion, with open
complement $j:U\hookrightarrow T$, and let $A$ be a finite ring.
On the small etale sites, the
direct image $i_*$ has a right
adjoint $Ri^!$ on the
ordinary derived categories.
The functor $i^*$ below is the
inverse image.

## Proof

For an etale module sheaf $N$, set
$\Gamma_ZN=\ker(N\to j_*j^*N)$.
The stalk description and the conservativity in
[lemma-weil-pbc-geometric-stalk-conservative] identify sheaves whose
restriction to $U$ is zero with sheaves on $Z$, by the exact fully
faithful $i_*$. Its inverse on these sheaves is the $i^*$ of
[def-weil-pbc-inverse-image]. Every map $i_*M\to N$ factors
uniquely through $\Gamma_ZN$; thus $i^!=i^*\Gamma_Z$ is right
adjoint to $i_*$ on sheaves.

Take a K-injective resolution $K\to I$ with injective terms, using
[prop-weil-pbc-kinjective-resolutions-exist]. Both $j^*I$ and
$i^!I$ are K-injective: their left adjoints $j_!$ and $i_*$
are exact, so Hom from an acyclic complex into either restriction is
acyclic. The complex-level adjunction gives
$i_*\dashv Ri^!$. Here derived direct image is that of
[def-weil-pbc-direct-image]; no constructibility has been used.
