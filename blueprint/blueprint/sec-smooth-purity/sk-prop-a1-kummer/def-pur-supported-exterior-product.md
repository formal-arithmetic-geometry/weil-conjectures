+++
id = "def-pur-supported-exterior-product"
kind = "definition"
title = "Exterior product in cohomology with closed support"
order = 1938
uses = ["def-kun-derived-tensor", "def-kun-kunneth-map", "def-pur-support-cohomology", "def-weil-scheme-morphism-properties"]
+++
Let $Z\subset X,W\subset Y$ be closed subschemes of
separated finite-type
schemes over an algebraically closed field $k$. Fix a finite
commutative coefficient ring $A$, and let $K,L$ be bounded-below
complexes of $A$-module sheaves on their etale sites whose
derived exterior product
is bounded below. The *supported exterior product* is the map

$$
\kappa^{Z,W}_{K,L}:
R\Gamma_Z(X,K)\otimes_A^LR\Gamma_W(Y,L)
\longrightarrow
R\Gamma_{Z\times W}(X\times_kY,K\boxtimes_A^L L).
$$

It is obtained by pulling back sections in the two factors and
tensoring them: their supports meet in $Z\times W$.
Derive this pairing with K-flat tensor and injective support
resolutions. Thus its composition with the map forgetting support
is the ordinary exterior product,
and its cohomology uses the
support functors.
