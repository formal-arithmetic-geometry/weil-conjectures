+++
id = "thm-pur-vector-bundle-thom"
kind = "theorem"
title = "Vector-bundle Thom isomorphism"
order = 1989
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-vector-bundle-thom-class", "def-pur-vector-bundle-zero-section", "def-weil-derived-cohomology-sheaves", "def-weil-derived-tensor", "def-weil-scheme-morphism-properties", "lem-pur-cfiber-stalk", "lem-pur-kunneth-supported", "thm-pur-localized-top-chern", "thm-pur-projective-bundle-formula", "thm-pur-rank-one-local-calculation", "thm-pur-rank-one-thom"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $\pi:E\to B$ be a vector bundle of constant rank $r$ with zero
section $z$. The morphism
$\tau_E:\Lambda_B\to R\pi_!\Lambda_E(r)[2r]$ of
[def-pur-vector-bundle-thom-class] is an isomorphism, compatible
with base change and with direct sums of vector bundles. Its inverse
is the *vector-bundle trace*

$$
\operatorname{tr}_\pi:R\pi_!\Lambda_E(r)[2r]\longrightarrow\Lambda_B.
$$

## Proof

Trivialize the bundle as in [def-pur-vector-bundle-zero-section]; the rank-one factors are those of [thm-pur-rank-one-thom], and their supported exterior product is the comparison of [lem-pur-kunneth-supported].
Step 1: on a geometric fiber. Let $\bar b\to B$ be a geometric
point. By [lem-pur-cfiber-stalk], the stalk of $\tau_E$ at
$\bar b$ is the morphism

$$
\Lambda\longrightarrow
R\Gamma_c\bigl(\mathbf A^r_{\bar b},\Lambda(r)[2r]\bigr),
$$

the class of the origin being the exterior product of the $r$
rank-one classes (the class of $0\subset\mathbf A^r$ is the Künneth
product of the classes of the coordinates' zero divisors, which is the
generator fixed by the rank-one normalization of
[thm-pur-rank-one-local-calculation]; equivalently
$R\Gamma_c(\mathbf A^r,\Lambda)\cong\Lambda(-r)[-2r]$ by the Künneth
result of [thm-pur-projective-bundle-formula] Step 1). The map
on the cohomology sheaves is therefore the
def:coefficient-twists-canonical identification $\Lambda\to\Lambda$,
hence an isomorphism at every geometric point.

Step 2: globally. The cone of the globally defined $\tau_E$ is a
bounded constructible complex with zero geometric stalks, hence zero
(the truncation argument of [def-weil-derived-cohomology-sheaves]).
Base change and direct sums: by (L2) and (L3) of
[thm-pur-localized-top-chern] and the base-change compatibility
of [def-pur-vector-bundle-thom-class]. No local morphism is
glued here.
