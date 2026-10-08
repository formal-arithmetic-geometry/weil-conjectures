+++
id = "lem-sf-triangle-two-out-of-three"
kind = "lemma"
title = "Isomorphism on two terms of a distinguished triangle"
order = 1863
uses = ["def-sf-datum", "def-weil-derived-cohomology-sheaves"]
+++
In the setting of [def-sf-datum], let $\Phi,\Psi$ be exact functors
between triangulated categories and let $\alpha:\Phi\to\Psi$ be a natural
transformation. If $\alpha$ is an isomorphism on two terms of a
distinguished triangle, then it is an isomorphism on the third.

## Proof

Apply the
cohomology functors $H^q$ to the map of triangles induced by $\alpha$: the
hypothesis gives a ladder of long exact sequences in which two of the three
columns are isomorphisms, so the third is an isomorphism by the five lemma;
a morphism whose cone has vanishing cohomology is zero in the derived
category, by [def-weil-derived-cohomology-sheaves].
