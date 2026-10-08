+++
id = "lem-weil-pbc-mittag-leffler"
kind = "lemma"
title = "Mittag--Leffler vanishing"
order = 2731
uses = ["def-weil-pbc-derived-inverse-limit", "prop-weil-pbc-roos-triangle"]
+++
A tower of finite abelian groups satisfies the Mittag--Leffler condition and
has $\varprojlim{}^1=0$. Consequently, for the derived inverse-limit
construction of [def-weil-pbc-derived-inverse-limit], the canonical Milnor
map is an isomorphism for such a tower.

(*Source note:* the vanishing is Stacks Project, More on Algebra, Lemma
15.88.1 (3) (Tag [07KW](https://stacks.math.columbia.edu/tag/07KW): if
$(A_n)$ is Mittag--Leffler then $R^1\lim A_n=0$, i.e. the system is right
acyclic for $\lim$), and the identification of the Milnor map is Lemma
15.88.10 (Tag [07KY](https://stacks.math.columbia.edu/tag/07KY)). Stacks
states these for towers of abelian groups; the form used here is a tower of
finite abelian groups in the tower category over $T_{\Proet}$, finiteness
being what forces the Mittag--Leffler condition, and the conclusion is stated
for the canonical Milnor map of [def-weil-pbc-derived-inverse-limit].)

## Proof

Descending chains of subgroups of a finite group stabilize, so the tower is
Mittag--Leffler and $\varprojlim{}^1=0$ by the product-cokernel description
of $\varprojlim{}^1$; the exact sequence of
[prop-weil-pbc-roos-triangle] then identifies the Milnor map.
