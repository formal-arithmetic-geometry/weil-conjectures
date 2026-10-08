+++
id = "def-weil-pbc-rational-category"
kind = "definition"
title = "Rational category from an integral category"
order = 1305
uses = ["def-weil-karoubi-envelope", "def-weil-pbc-bounded-constructible-complete"]
+++
Let $E/\Ql$ be finite, let $\mathcal O_E$ be its ring of integers, and let
$\varpi$ be a uniformizer. Define
$$
 \Dbc(T,E)=
 \Dbc(T,\mathcal O_E)[1/\varpi],
$$
the *rationalization* (raw scalar localization) of the integral category
[def-weil-pbc-bounded-constructible-complete]: it has the same objects as
$\Dbc(T,\mathcal O_E)$, and morphisms
$$
 \Hom(K,L)[1/\varpi]
 =\Hom_{\Dbc(T,\mathcal O_E)}(K,L)\otimes_{\mathcal O_E}E.
$$
No Karoubi envelope is taken in this definition. That the category is
idempotent complete, and that the canonical functor into the Karoubi
envelope is consequently an exact equivalence, is recorded with the other
properties of this construction.
