+++
id = "lem-kun-colim-gbl-gen"
kind = "lemma"
title = "Filtered colimits of globally generated sheaves"
order = 1706
uses = ["def-kun-global-generated", "def-weil-pbc-geometric-stalks", "lem-kun-global-generated-stalkwise", "lem-kun-stalks-commute-colimits", "prop-weil-pbc-geometric-stalks-exact"]
+++
A filtered colimit of globally generated sheaves of abelian groups on
a site is globally generated.

## Proof

Let $F=\varinjlim_iF_i$. By [prop-weil-pbc-geometric-stalks-exact]
and the commutativity of stalks with filtered colimits
([lem-kun-stalks-commute-colimits]),
$F_{\bar x}=\varinjlim_i(F_i)_{\bar x}$, each $(F_i)_{\bar x}$ being
mapped onto by $H^0(T_{\Et},F_i)$; filtered colimits of abelian
groups preserve surjection, so the evaluation map of
[def-kun-global-generated] is surjective on every stalk, and
stalkwise surjectivity is global generation by
[lem-kun-global-generated-stalkwise].
