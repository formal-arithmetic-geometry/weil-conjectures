+++
id = "lem-exc-proetale-support-triangle"
kind = "lemma"
title = "Pro-etale closed-support triangle before constructible restriction"
order = 1866
uses = ["def-weil-derived-direct-image", "def-weil-open-closed-recollement", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-exc-proetale-closed-essential-image", "lem-exc-proetale-closed-support", "prop-exc-open-adjoint", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
Let $T$ be Noetherian, let $i:Z\hookrightarrow T$ be a
closed immersion, and
let $j$ be its open complement. For a finite ring $A$, let
$Ri^!$ denote the right adjoint of the
direct image $i_*$ on the
pro-etale sites, taken on
the ambient ordinary derived categories, and let $Rj_*$ and $j^*$
be the direct image and the
inverse image of the open immersion $j$. In addition to the
open–closed triangle,
one has

$$
i_*Ri^!K\longrightarrow K\longrightarrow Rj_*j^*K
\longrightarrow i_*Ri^!K[1]
\qquad(K\in D(T_{\mathrm{proet}},A)).
$$

No constructibility of $Ri^!K$ is part of this assertion.

## Proof

Choose a K-injective complex $I$ with injective terms resolving
$K$, by [prop-weil-pbc-kinjective-resolutions-exist]; by
[lem-exc-proetale-closed-support] this resolution computes the
ambient right adjoint, so $Ri^!K=i^!I$ for the sheaf-level $i^!$
constructed there. Exactness of the left adjoint $j_!$
in [prop-exc-open-adjoint] makes $j^*I$ K-injective,
so $Rj_*j^*K\simeq j_*j^*I$. For each injective term
the restriction $I^q\to j_*j^*I^q$ is surjective: a section over
the open part of a site object is a morphism from its free module
sheaf, the free module sheaf of the open part embeds in that of the
whole object, and injectivity extends the corresponding map to
$I^q$. By
[lem-exc-proetale-closed-essential-image] the kernel of
this restriction is $i_*$ of a module sheaf supported on $Z$,
namely $i_*i^!I^q$. The degreewise short exact sequences

$$
0\longrightarrow i_*i^!I^q\longrightarrow I^q
\longrightarrow j_*j^*I^q\longrightarrow0
$$

therefore assemble into a short exact sequence of complexes whose
first term is $i_*i^!I$; the associated triangle in the ordinary
derived categories of the pro-etale site is the displayed one, and no
constructibility of $Ri^!K$ has been used.
