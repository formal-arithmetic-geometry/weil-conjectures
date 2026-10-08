+++
id = "lem-exc-closed-support-triangle"
kind = "lemma"
title = "Closed-support triangle before restriction"
order = 1804
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-etale-site", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lem-exc-closed-ambient", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $i:Z\hookrightarrow T$ be a
closed immersion, with open
complement $j:U\hookrightarrow T$, and let $A$ be a finite ring.
Let $Ri^!$ denote the right adjoint of the
direct image $i_*$ on the
small etale sites, taken on the
ordinary derived categories,
and let $Rj_*$, $j^*$ be the
direct image and the
inverse image of the open
immersion $j$. Then for every $K\in D(T_{\mathrm{et}},A)$ there is
a natural distinguished triangle

$$
i_*Ri^!K\longrightarrow K\longrightarrow Rj_*j^*K
\longrightarrow i_*Ri^!K[1].
$$

No constructibility is assumed of the values of this right adjoint.

## Proof

Choose a K-injective resolution $K\to I$ with injective terms, using
[prop-weil-pbc-kinjective-resolutions-exist]; by
[lem-exc-closed-ambient] the right adjoint $Ri^!$ of the statement
is computed on such a resolution, so $Ri^!K=i^!I$ for the sheaf-level
functor $i^!=i^*\Gamma_Z$ constructed there. Both $j^*I$ and
$i^!I$ are K-injective: their left adjoints $j_!$ and $i_*$ are
exact, so Hom from an acyclic complex into either restriction is
acyclic; in particular $Rj_*j^*K\simeq j_*j^*I$. For each injective
term $I^q$, the map $I^q\to j_*j^*I^q$ is surjective. Indeed, a section
on the open part of an etale object extends because the inclusion of its
free module sheaf into that of the whole object is a monomorphism, and
injectivity extends the corresponding map to $I^q$.
Consequently the degreewise exact sequence

$$
0\longrightarrow i_*i^!I\longrightarrow I
\longrightarrow j_*j^*I\longrightarrow0
$$

gives the asserted triangle. The functors $i_*$, $Rj_*$, $j^*$
used here are the direct image and inverse image of
[def-weil-pbc-direct-image], [def-weil-pbc-inverse-image]; no
constructibility has been used.
