+++
id = "lem-exc-closed-lift-units"
kind = "lemma"
title = "Units of the ind-etale lift"
order = 1840
uses = ["def-exc-ind-etale-closed-lift", "lem-exc-closed-lift-filtered"]
+++
An element of $H_A(\overline C)$, as constructed in
[def-exc-ind-etale-closed-lift], is invertible if its image in $\overline C$
is invertible.

## Proof

Represent the element by $b\in B$ at a stage of the filtered colimit of
[def-exc-ind-etale-closed-lift], [lem-exc-closed-lift-filtered]. Since the
image of $b$ is invertible in $\overline C$, the localization $B_b$, with
its extended map to $\overline C$, is another object of the indexing
category. The transition $B\to B_b$ makes the given element invertible in
the colimit.
