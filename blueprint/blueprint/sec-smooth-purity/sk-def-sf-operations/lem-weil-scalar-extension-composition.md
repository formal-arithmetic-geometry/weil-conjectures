+++
id = "lem-weil-scalar-extension-composition"
kind = "lemma"
title = "Composition of scalar extensions"
order = 1469
uses = ["def-weil-rationalization-karoubi", "prop-weil-pbc-scalar-extension"]
+++
Let $E\subset L\subset M$ be finite extensions of $\Ql$ and let $Y$ be a
scheme. For every object $K$ of the rationalized category $D^b_c(Y,E)$ of
[def-weil-rationalization-karoubi] there is a canonical isomorphism

$$
 (K\otimes_EL)\otimes_LM\xrightarrow{\ \sim\ }K\otimes_EM
$$

in $D^b_c(Y,M)$, natural in $K$ and compatible with the identity extension;
that is, the scalar-extension functors of
[def-weil-rationalization-karoubi] are compatible with composition of finite
extensions.

## Proof

On integral representatives the two composites are both computed, in the two
possible orders, from the completed derived tensor product with $\mathcal
O_M$; the associativity isomorphism of the derived tensor product identifies

$$
 (K\widehat\otimes^L_{\mathcal O_E}\mathcal O_L)
 \widehat\otimes^L_{\mathcal O_L}\mathcal O_M
 \cong K\widehat\otimes^L_{\mathcal O_E}\mathcal O_M.
$$

The second tensor product is over $\mathcal O_L$, as required by the tower of
finite free coefficient extensions. The levelwise reductions and the
rationalization of [def-weil-rationalization-karoubi] commute with this
identification. After rationalization the comparison is the composite of
associators recorded in the scalar-extension proposition of the
proper-base-change chapter, which also supplies naturality in the object and
the unit and pentagon equations. All categories and functors involved are
those of [def-weil-rationalization-karoubi].
