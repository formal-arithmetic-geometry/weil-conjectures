+++
id = "lemma-weil-pbc-finite-pullback-composition"
kind = "lemma"
title = "Finite pullback composition"
order = 1081
uses = ["def-weil-pbc-finite-section-pullback", "lemma-weil-pbc-finite-pullback-identity"]
+++
For finite $T''\xrightarrow{v}T'\xrightarrow{u}T$,
$(uv)_V^\sharp(s)=v_{V\times_TT'}^\sharp(u_V^\sharp(s))$ under the
associativity isomorphism of fibre products.

## Proof

Both sections are the image of the same presheaf section $s$ under the
composite inverse-image functor. Naturality of sheafification and the
associativity isomorphism make the two unit maps equal.
