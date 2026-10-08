+++
id = "def-nagata-qc-open-complement-ideal"
kind = "definition"
title = "Finite-type ideal attached to a quasi-compact open"
order = 169
lean = ["AlgebraicGeometry.Scheme.exists_finiteType_ideal_coe_support_eq_compl"]
uses = ["def-nagata-extended-ideal", "lemma-nagata-finite-type-ideal-extension-exists", "lemma-nagata-qc-open-complement-ideal-exists"]
+++
Let $W\subseteq Y$ be a quasi-compact open in a qcqs scheme. Choose one
witness supplied by
[lemma-nagata-qc-open-complement-ideal-exists] and define
$\mathcal I_Y(W)$ to be its ideal component. Finiteness, quasi-coherence,
and the vanishing-set identity are specification fields, not additional
assertions in this definition.
