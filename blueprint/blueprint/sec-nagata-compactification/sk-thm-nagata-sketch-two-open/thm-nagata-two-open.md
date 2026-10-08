+++
id = "thm-nagata-two-open"
kind = "theorem"
title = "[stacks-project]"
order = 305
lean = ["AlgebraicGeometry.HasCompactification.of_two_open_cover"]
uses = ["def-nagata-admissible-blowup", "def-nagata-common-modification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-global-blowup", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-compactification-candidate", "def-nagata-two-open-final-modification", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-boundary-loci", "lemma-nagata-common-modification", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-dense-source-valuative", "lemma-nagata-intermediate-separated", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-one-valuation-avoids-boundary", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-proper-valuative-criterion-existence-api", "lemma-nagata-separated-valuation-lift-unique", "lemma-nagata-two-open-candidate-proper", "lemma-nagata-two-open-density-transport", "lemma-nagata-two-open-final-modification", "lemma-nagata-valuation-open-closed-point", "lemma-nagata-valuation-pair-factors-comparison", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
The constructed factorization $\mathsf C_{12}(U/S)$ is a compactification
of $U\to S$. Consequently $U\to S$ is compactifiable.

## Proof

By [lemma-nagata-two-open-final-modification], the first map
$j_W\colon U\to W$ is an open immersion and $W\to S$ is separated and of
finite type. It is proper by
[lemma-nagata-two-open-candidate-proper]. The open immersion $j_W$ is
quasi-compact by
[lemma-nagata-open-immersion-qc-over-separated-target], applied to the
triangle $U\to W\to S$. The defining gluing maps give the factorization
equality, so all fields of [def-nagata-compactification] are present.
