+++
id = "lem-fin-finite-morphism"
kind = "lemma"
title = "Finite direct images of constructible sheaves"
order = 1580
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-finite-pushforward-constructible-noetherian", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-stalk-formula", "sbc-def-coefficient-conventions"]
+++
Let $f:X\to S$ be finite
with $S$ of finite type over $k$, and let $F$ be a
constructible
$\Lambda$-sheaf on $X_{{\mathrm{et}}}$. Then the direct image
$f_*F$ of [def-weil-pbc-direct-image] is constructible on
$S_{{\mathrm{et}}}$ and $R^qf_*F=0$ for every $q>0$.

## Proof

Exactness and vanishing of positive direct images are
[lemma-weil-pbc-finite-direct-image-exact]. Apply
[lem-weil-pbc-finite-pushforward-constructible-noetherian]
to the underlying finite constructible abelian sheaf of $F$.
It gives a finite partition on which $f_*F$ is finite locally
constant as an abelian sheaf. On an etale trivialization with
finite group fibre $M$, the action of each $\lambda\in\Lambda$
is specified by its values on the finite set $M$.
After an etale refinement these finitely many values are constant;
the addition and module relations remain the given relations.
Thus the trivialization is one of constant $\Lambda$-modules.
This is module constructibility in the sense of
[def-weil-pbc-constructible-complexes]. The argument does
not use an embedding into a finite constant pushforward.
