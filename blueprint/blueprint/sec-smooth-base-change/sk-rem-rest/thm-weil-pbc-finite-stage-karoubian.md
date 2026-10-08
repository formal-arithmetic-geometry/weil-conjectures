+++
id = "thm-weil-pbc-finite-stage-karoubian"
kind = "theorem"
title = "Finite-stage rational categories are Karoubian"
order = 1433
uses = ["def-weil-pbc-rational-category", "def-weil-t-structure", "prop-weil-localized-tstructure", "thm-weil-karoubian-bounded-t"]
+++
For $E/\Ql$ finite, the category $\Dbc(T,E)$
[def-weil-pbc-rational-category] is idempotent complete, and the canonical
functor $\Dbc(T,E)\to\Kar(\Dbc(T,E))$ is an exact equivalence.

*Source note:* no Stacks Project entry states this form: Stacks has no
idempotent completion (Homological Algebra, Section 12.4, [Tag
09SF](https://stacks.math.columbia.edu/tag/09SF), states only the Karoubian
property, Definition 12.4.1, [Tag
09SG](https://stacks.math.columbia.edu/tag/09SG), with the splitting
criterion of Lemma 12.4.2, [Tag
09SH](https://stacks.math.columbia.edu/tag/09SH), and the criteria of Lemma
12.4.3, [Tag 05QV](https://stacks.math.columbia.edu/tag/05QV)) and no
t-structure, so the Karoubianity of a triangulated category carrying a
bounded t-structure is not available; the blueprint adds the Karoubianity of
the finite-stage rational categories, deduced from the bounded t-structure
of [prop-weil-localized-tstructure] and the Karoubianity theorem for bounded
t-structures proved in this manuscript.

## Proof

By [prop-weil-localized-tstructure] the category $\Dbc(T,E)$
[def-weil-pbc-rational-category] carries a bounded t-structure, so the
Karoubianity theorem for bounded t-structures applies.
