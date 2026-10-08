+++
id = "lem-weil-finite-compact-projection-formula"
kind = "lemma"
title = "Finite-coefficient compact-support projection formula"
order = 1878
uses = ["def-cbc-exchange-map", "def-compact-support-direct-image-detailed", "def-exchange-projection", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-pbc-derived-categories", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-etale-sheaves", "def-weil-scheme-morphism-properties", "fix-lem-finite-tor-perfect", "lemma-weil-pbc-geometric-stalk-conservative", "thm-cbc-finite-level-proetale", "thm-cbc-finite-torsion", "thm-weil-pbc-site-comparison"]
+++
Fix the finite-field datum
and finite coefficient ring $A=A_{E,n}$.
Let $f:X\to Y$ be a
separated finite-type
morphism of finite-type $k$-schemes.
On the small etale sites, let
$K\in D^b_c(X_{\mathrm{et}},A)$ and
$L\in D^b_c(Y_{\mathrm{et}},A)$, in the
derived categories of
bounded complexes with constructible cohomology.
Assume $L$ has
finite Tor amplitude,
using the same tensor-vanishing definition on the etale site.
The projection transformation,
formed with the
derived tensor and pullback
and the compact-support
direct image, is an isomorphism:

$$
Rf_!K\otimes_A^L L
\xrightarrow{\ \sim\ } Rf_!(K\otimes_A^L Lf^*L).
$$

It is natural in $K,L$.
The same assertion holds for their pro-etale realizations equipped
with etale-origin witnesses,
where the representatives satisfy the displayed hypotheses.

## Proof

First work on the etale site. Choose a compactification
$f=p\circ j$. By [def-compact-support-direct-image-detailed],
$Rf_!=Rp_*j_!$. The map of [def-exchange-projection]
is the composite of the direct-image projection map for $p$
and

$$
j_!K\otimes_A^L p^*L
\cong j_!(K\otimes_A^L f^*L).
$$

The latter isomorphism can be checked on etale stalks: on the open
subset both maps are the identity, and off it both terms are zero.
The same calculation works with K-flat representatives for the
[def-weil-derived-pullback-tensor-hom] derived tensor product.

Let $\bar y:\operatorname{Spec}\Omega\to Y$ be a geometric point,
let $X_{\bar y}=X\times_Y\operatorname{Spec}\Omega$, and write
$K_{\bar y}^{\mathrm{fib}}$ for the pullback of $K$ to this fiber
and $P=L_{\bar y}\in D(A)$.
Compact-support base change [thm-cbc-finite-torsion]
and exactness of geometric stalks identify the stalk of the
displayed projection map with

$$
R\Gamma_c(X_{\bar y},K_{\bar y}^{\mathrm{fib}})\otimes_A^L P
\longrightarrow
R\Gamma_c(X_{\bar y},
K_{\bar y}^{\mathrm{fib}}\otimes_A^L\underline P).
$$

Here $\underline P$ is the pullback of the complex of $A$-modules
$P$ from $\operatorname{Spec}\Omega$.
Both base-change applications are legitimate: finite Tor amplitude
of $L$ makes $K\otimes_A^L f^*L$ bounded below.

This identification concerns the actual projection map.
Indeed the exchange map in [def-cbc-exchange-map] is obtained
from proper base change and the open-immersion base-change map.
For the proper part, transposing either order of exchange and
projection gives the same composite: pull back
$Rp_*j_!K\otimes L$, apply the counit
$p^*Rp_*j_!K\to j_!K$ to the first factor, and retain the
pullback of $L$ in the second factor.
For the open part, both composites are the identity on the open
stalks and zero on the complementary stalks. Thus the exchange
identifications carry the chosen projection map to the fiber map.

The stalk-perfectness lemma [fix-lem-finite-tor-perfect]
gives a bounded finite-free representative of $P$.
For fixed $K_{\bar y}^{\mathrm{fib}}$, the two sides of the fiber
map are exact functors of $P$ on bounded complexes of finite
projective $A$-modules, and the displayed map is a natural
transformation of these functors.
For $P=A$ it is the unit identification, hence an isomorphism.
It remains an isomorphism after finite direct sums, shifts,
mapping cones, and direct summands: for cones use the long exact
cohomology sequences, and for summands restrict the inverse along
the splitting maps.
Successive truncation by terms builds every bounded finite-free
complex from finite sums of shifts of $A$.
It follows that the fiber map is an isomorphism for this $P$.
Every geometric stalk of the cone of the original projection map
therefore vanishes. Conservativity on the etale site,
[lemma-weil-pbc-geometric-stalk-conservative], proves that its
cone is zero. Naturality follows from the construction.

For the pro-etale assertion, use the specified representatives in
[def-weil-pbc-etale-origin-witness].
The exact comparison inverse image of
[thm-weil-pbc-site-comparison] commutes with tensor and
pullback, while the compact-support comparison used in
[thm-cbc-finite-level-proetale] identifies the transported
$Rp_*j_!$ and its exchange maps.
The same counit computation above identifies the transported
projection map with the pro-etale one. Transporting the etale
isomorphism proves the assertion for these realizations.
