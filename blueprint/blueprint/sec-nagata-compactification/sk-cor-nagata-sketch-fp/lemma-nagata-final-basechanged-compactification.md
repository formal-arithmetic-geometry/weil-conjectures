+++
id = "lemma-nagata-final-basechanged-compactification"
kind = "lemma"
title = "Property of the base-changed compactification"
order = 378
lean = ["AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation"]
uses = ["def-nagata-compactifiable", "def-nagata-final-basechanged-compactification", "def-nagata-noetherian-inverse-system", "lemma-nagata-compactification-base-change", "lemma-nagata-final-descended-model", "lemma-nagata-final-noetherian-compactification", "lemma-nagata-separated-eventually", "prop-nagata-noetherian-inverse-system", "thm-nagata-noetherian"]
+++
Let $S$ be quasi-compact and quasi-separated and let $Y\to S$ be
separated and of finite presentation. The constructed
$\mathsf C^{\mathrm{fp}}(Y/S)$ of
[def-nagata-final-basechanged-compactification] is a compactification of
$Y\to S$; in particular $Y\to S$ is compactifiable.

## Proof

Base change preserves every compactification field by
[lemma-nagata-compactification-base-change]. Transporting the source
across the isomorphism $\epsilon_Y$ preserves the open-immersion,
quasi-compactness, properness, and factorization equalities.
