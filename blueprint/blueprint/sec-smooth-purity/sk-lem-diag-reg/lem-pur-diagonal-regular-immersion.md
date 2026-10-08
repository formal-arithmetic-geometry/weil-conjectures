+++
id = "lem-pur-diagonal-regular-immersion"
kind = "lemma"
title = "The diagonal is a regular immersion"
order = 2004
uses = ["def-pur-conventions", "def-pur-regular-immersion", "def-sbc-smooth-morphisms", "def-weil-scheme-morphism-properties", "sbc-thm-etale-local-normal-form"]
lean = ["AlgebraicGeometry.isRegularImmersion_diagonal"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be smooth,
separated, of pure
relative dimension $d$, and put $W=X\times_YX$ with projections
$p_1,p_2$ and diagonal $\Delta:X\hookrightarrow W$. Then $\Delta$
is a regular closed immersion of
pure codimension $d$, and its normal bundle is canonically

$$
N_{\Delta/W}\;\cong\;T_{X/Y}
$$

(the relative tangent bundle of $f$).

## Proof

By [sbc-thm-etale-local-normal-form], $f$ is etale locally the
projection $\mathbf A^d_Y\to Y$; on the model, $\Delta$ is the zero
section of $\mathbf A^d$, a regular closed immersion of codimension
$d$ with normal bundle the trivial rank-$d$ bundle, which under the
identification is $T_{X/Y}$. Regular immersions, their codimension
and their normal bundles are etale local (and compatible with etale
base change), hence the assertion.
