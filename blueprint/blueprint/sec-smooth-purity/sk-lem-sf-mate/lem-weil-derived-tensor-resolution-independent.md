+++
id = "lem-weil-derived-tensor-resolution-independent"
kind = "lemma"
title = "Resolution independence of the derived tensor product"
order = 1870
uses = ["def-weil-derived-tensor", "def-weil-pbc-proetale-site"]
+++
Fix a scheme $Y$, a commutative ring $A$, and complexes $K_1,K_2$ of
$A_Y$-modules on the small pro-etale site
[def-weil-pbc-proetale-site] $Y_{\mathrm{proet}}$. Let $P\to K_1$
and $P'\to K_1$ be quasi-isomorphisms of complexes of $A_Y$-modules whose
sources are K-flat [def-weil-derived-tensor]. Then the induced map

$$
 P\otimes_AK_2\longrightarrow P'\otimes_AK_2
$$

is a quasi-isomorphism. Consequently the object $K_1\otimes_A^LK_2$ of
[def-weil-derived-tensor] is independent of the chosen K-flat resolution, up
to canonical isomorphism in $D(Y_{\mathrm{proet}},A)$.

## Proof

Over a ring, a quasi-isomorphism $\alpha:P\to Q$ between K-flat complexes
induces a quasi-isomorphism
$\operatorname{id}_L\otimes\alpha:\operatorname{Tot}(L\otimes P)\to
\operatorname{Tot}(L\otimes Q)$ for every complex $L$: this is Lemma 15.60.12
of the Stacks Project, Tag
[064L](https://stacks.math.columbia.edu/tag/064L), whose proof uses only the
K-flatness [def-weil-derived-tensor] of the two complexes, the existence of
K-flat resolutions (Tag
[06Y4](https://stacks.math.columbia.edu/tag/06Y4)) and the behaviour of
K-flatness under tensoring (Tag
[06Y0](https://stacks.math.columbia.edu/tag/06Y0)). For complexes of
$A_Y$-modules on the small pro-etale site
[def-weil-pbc-proetale-site] the same argument applies: tensor
products, total complexes and truncations are formed termwise in the abelian
category of sheaves of $A_Y$-modules, in which filtered colimits are exact,
and K-flat resolutions exist by the functorial flat-resolution construction.
Since $P$ and $P'$ are both K-flat resolutions of $K_1$, the identity of
$K_1$ lifts to a morphism $P\to P'$ in the homotopy category of complexes
(Tag [0G6M](https://stacks.math.columbia.edu/tag/0G6M)), and the resulting
map $P\otimes_AK_2\to P'\otimes_AK_2$ is a quasi-isomorphism by the first
part. This is the assertion recorded for modules in Definition 15.60.13 of
the Stacks Project, Tag
[064M](https://stacks.math.columbia.edu/tag/064M) (the category of K-flat
resolutions of $K_1$ is cofiltered and Lemma 15.60.12 shows that the functor
obtained is independent of the choice).
