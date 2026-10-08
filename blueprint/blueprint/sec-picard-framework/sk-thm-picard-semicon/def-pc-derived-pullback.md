+++
id = "def-pc-derived-pullback"
kind = "definition"
title = "Derived pullback of modules on schemes"
order = 665
uses = ["def-pc-derived-category", "def-pc-scheme", "def-weil-derived-tensor"]
+++
For a morphism $g:T\to S$ of schemes,
let $Lg^*:D(\mathcal O_S)\to D(\mathcal O_T)$ be the left derived
functor of module pullback. Explicitly it is

$$
Lg^*E=\mathcal O_T\otimes^{\mathbf L}_{g^{-1}\mathcal O_S}g^{-1}E.
$$

The derived tensor product
is computed by a K-flat resolution.
