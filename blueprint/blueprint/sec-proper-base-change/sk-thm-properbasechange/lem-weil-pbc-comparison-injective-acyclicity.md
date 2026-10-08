+++
id = "lem-weil-pbc-comparison-injective-acyclicity"
kind = "lemma"
title = "Acyclicity of the pulled-back etale injectives"
order = 1284
uses = ["def-weil-pbc-cover-cech", "def-weil-pbc-etale-cohomology", "def-weil-pbc-ind-etale-basis", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-cech-criterion", "lem-weil-pbc-comparison-sections", "lem-weil-pbc-etale-finite-data-descent", "lem-weil-pbc-etale-section-continuity", "lem-weil-pbc-ind-etale-basis", "lem-weil-pbc-ind-etale-stability", "lem-weil-pbc-proetale-restriction-injectives"]
+++
If $X$ is affine and $I$ is injective in etale module sheaves on $X$, then

$$
 H^q(U_{\Proet},(\nu_X^*I)|_U)=0
 \quad(U\in\mathcal B_X,\ q>0).
$$

Here the left side is derived evaluation on the basis object $U$.

## Proof

By [lem-weil-pbc-ind-etale-basis] and [lem-weil-pbc-cech-criterion], it
suffices to prove positive Cech vanishing on every finite basis covering
$\{V_a\to U\}$. There are two separate limits in this calculation.

First write each $V_a$ as a limit of affine etale finite-presentation
$U$-schemes, using the stability lemma for ind-etale algebras. Every finite
choice of stages still covers $U$. As in the proof of
[lem-weil-pbc-comparison-sections], section continuity on all finite
intersections writes the Cech complex of [def-weil-pbc-cover-cech] as the
filtered colimit of those for these etale coverings of $U$. Exactness of
filtered colimits gives the same identity on Cech cohomology.

Second, fix one such finite etale covering $\{W_a\to U\}$, and write
$U=\varprojlim_iU_i$ with $U_i$ affine etale over $X$. The covering descends
to a finite etale covering $\{W_{a,i}\to U_i\}$ at a sufficiently late stage,
by the descent of finite-presentation data at an inverse limit; all its
finite intersections descend by base change. The same section continuity and
exactness of filtered colimits give

$$
 \check H^q(\{W_a\to U\},\nu_X^*I)
 =\varinjlim_i\check H^q(\{W_{a,i}\to U_i\},I).
$$

On the right every term is an etale object over $X$; the identification of
its sections with those of $I$ is [lem-weil-pbc-comparison-sections].
Injectivity of $I$ and the first assertion of
[lem-weil-pbc-cech-criterion] make the right side zero for $q>0$. Both limits
therefore give zero, and the criterion proves the claimed derived vanishing.
The identification with cohomology on $U_{\Proet}$ is
[lem-weil-pbc-proetale-restriction-injectives]. This supplies the geometric
step in [Stacks Project, Tag
099U](https://stacks.math.columbia.edu/tag/099U) without assuming it as part
of the site comparison.
