+++
id = "lem-weil-pbc-comparison-sections"
kind = "lemma"
title = "Sections of the comparison inverse image"
order = 1283
uses = ["def-weil-pbc-cover-cech", "def-weil-pbc-ind-etale-basis", "def-weil-pbc-inverse-image", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-etale-finite-data-descent", "lem-weil-pbc-etale-section-continuity", "lem-weil-pbc-ind-etale-basis", "lem-weil-pbc-ind-etale-stability"]
+++
Let $X$ be affine, let $F$ be an etale module sheaf, and write a basis object
as $U=\varprojlim_i U_i$ with $U_i/X$ affine etale of finite presentation.
Then naturally

$$
 (\nu_X^*F)(U)=\Gamma(U_{\Et},F|_U)
             =\varinjlim_i F(U_i).
$$

The restriction $F|_U$ is the scheme inverse image. The same section formula
holds for sheaves of sets.

## Proof

Define $P_F(U)=\Gamma(U_{\Et},F|_U)$ on the basis. The second equality in the
statement is the continuity of sections at an inverse limit; restriction of
an etale sheaf to an etale object is evaluation on its slice. We verify that
$P_F$ is already a sheaf for the finer topology. Let $\{V_a\to U\}$ be a
finite basis covering. By the stability lemma for ind-etale algebras write
$V_a=\varprojlim_\lambda V_{a,\lambda}$, with each $V_{a,\lambda}\to U$
affine etale of finite presentation. Every finite choice of stages still
covers $U$, because its images contain the images of the covering $V_a$'s.
The fibre products in each degree of [def-weil-pbc-cover-cech] commute with
these inverse limits. Section continuity, applied on these fibre products to
$F|_U$, therefore writes their section groups as the filtered colimit of the
finite-stage section groups. Finite products and kernels commute with
filtered colimits of modules. The etale sheaf equalizer at each finite stage
consequently proves the covering equalizer for $P_F$. By
[lem-weil-pbc-ind-etale-basis], it extends to the full site.

We identify it with the inverse image by its adjunction, so no comparison of
derived categories is being assumed here. Given $F\to\nu_{X,*}G$, each
presentation gives compatible maps $F(U_i)\to G(U_i)\to G(U)$, hence
$P_F(U)\to G(U)$. These maps are natural on the basis: a map from a limit to
a finite-presentation affine object factors through a stage, and equalities
of factorizations hold later, by the descent of finite-presentation data at
an inverse limit. Conversely a map $P_F\to G$ restricts to $F\to\nu_{X,*}G$,
since $P_F(U_i)=F(U_i)$ on etale objects. These constructions are inverse, as
every section of $P_F(U)$ is represented at a stage. They give precisely the
adjunction of [def-weil-pbc-site-comparison-morphism], proving the formula.
The sheaf and adjunction arguments use only finite products, equalizers, and
filtered colimits, and hence apply to sets too.
