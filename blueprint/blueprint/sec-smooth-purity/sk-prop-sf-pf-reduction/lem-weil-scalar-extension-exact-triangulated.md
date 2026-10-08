+++
id = "lem-weil-scalar-extension-exact-triangulated"
kind = "lemma"
title = "Scalar extension is an exact triangulated functor"
order = 1883
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-rationalization-karoubi", "lem-weil-scalar-extension-well-defined", "prop-weil-pbc-scalar-extension"]
+++
Let $E\subset L$ be a finite extension of $\Ql$ and let $Y$ be a scheme. The
scalar-extension functor

$$
 -\otimes_E L:D^b_c(Y,E)\longrightarrow D^b_c(Y,L)
$$

of [def-weil-rationalization-karoubi] is an exact triangulated functor: it
preserves shifts and carries distinguished triangles of $D^b_c(Y,E)$ to
distinguished triangles of $D^b_c(Y,L)$.

## Proof

The functor is well defined by [lem-weil-scalar-extension-well-defined]. On
integral representatives it is the derived tensor product
$-\otimes^L_{\mathcal O_E}\mathcal O_L$ of [def-weil-derived-tensor] composed
with the levelwise reductions of
[def-weil-derived-complete-integral-detailed] and the rationalization of
[def-weil-rationalization-karoubi]; being a composite of exact functors of
triangulated categories it preserves shifts and distinguished triangles. The
same statements, with the associators, shift comparisons and unit equations
of the normalized system, are recorded in the scalar-extension proposition of
the proper-base-change chapter, to which the present functor is the transport
along the identification of [def-weil-rationalization-karoubi] with the raw
scalar localization there.
