+++
id = "lemma-nagata-two-open-candidate-proper"
kind = "lemma"
title = "Properness of the two-open candidate"
order = 304
lean = ["AlgebraicGeometry.HasCompactification.of_two_open_cover"]
uses = ["def-nagata-admissible-blowup", "def-nagata-common-modification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-global-blowup", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-compactification-candidate", "def-nagata-two-open-final-modification", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-boundary-loci", "lemma-nagata-common-modification", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-dense-source-valuative", "lemma-nagata-final-density", "lemma-nagata-intermediate-separated", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-one-valuation-avoids-boundary", "lemma-nagata-proper-valuative-criterion-existence-api", "lemma-nagata-separated-valuation-lift-unique", "lemma-nagata-two-open-density-transport", "lemma-nagata-two-open-final-modification", "lemma-nagata-two-open-valuative-lifting", "lemma-nagata-valuation-open-closed-point", "lemma-nagata-valuation-pair-factors-comparison", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
The constructed structural morphism $W\to S$ is proper.

## Proof

The morphism $U_1\cap U_2\to W$ is quasi-compact and dense by
[lemma-nagata-final-density], and its valuation diagrams admit unique
lifts by [lemma-nagata-two-open-valuative-lifting]. The dense-source
valuative criterion makes $W\to S$ universally closed. It is separated
and of finite type by
[lemma-nagata-two-open-final-modification]; hence it is proper.
