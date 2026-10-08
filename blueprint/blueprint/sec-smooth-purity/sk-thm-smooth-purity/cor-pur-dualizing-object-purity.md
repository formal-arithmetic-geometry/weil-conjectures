+++
id = "cor-pur-dualizing-object-purity"
kind = "theorem"
title = "Smooth purity"
order = 2011
tags = ["latex:corollary"]
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-cohomological-smoothness", "thm-pur-diagonal-dualizing-object"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be smooth separated of pure relative dimension $d$
and let $K\in D^b_{ctf}(Y,\Lambda)$. Substituting the identification
of [thm-pur-diagonal-dualizing-object] into the tensor formula of
[thm-pur-cohomological-smoothness] gives the canonical
isomorphism

$$
Lf^*K(d)[2d]\;\xrightarrow{\ \sim\ }\;Rf^!K.
$$

Every map involved was normalized by the Kummer generator, so the Tate
twist, shift, and trace normalization are fixed canonically; the
identification is compatible with arbitrary base change and
composition.

## Proof

The composite is the twist reassociation of
[def-coefficient-twists-detailed], the inverse of the identification of
[thm-pur-diagonal-dualizing-object], and the tensor formula of
[thm-pur-cohomological-smoothness]; each is an isomorphism.
