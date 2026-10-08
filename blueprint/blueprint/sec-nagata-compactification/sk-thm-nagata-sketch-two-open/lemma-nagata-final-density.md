+++
id = "lemma-nagata-final-density"
kind = "lemma"
title = "Density after the final common modification"
order = 302
lean = ["AlgebraicGeometry.HasCompactification.of_two_open_cover"]
uses = ["def-nagata-admissible-blowup", "def-nagata-common-modification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-global-blowup", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-compactification-candidate", "def-nagata-two-open-final-modification", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-boundary-loci", "lemma-nagata-common-modification", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-dense-source-valuative", "lemma-nagata-intermediate-separated", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-one-valuation-avoids-boundary", "lemma-nagata-proper-valuative-criterion-existence-api", "lemma-nagata-separated-valuation-lift-unique", "lemma-nagata-two-open-density-transport", "lemma-nagata-two-open-final-modification", "lemma-nagata-valuation-open-closed-point", "lemma-nagata-valuation-pair-factors-comparison", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
The constructed map $U_1\cap U_2\to W$ is quasi-compact and has dense
image.

## Proof

Apply [lemma-nagata-two-open-density-transport] to the construction of
$W'_1,W'_2,W$. Its hypotheses hold because the selected compactifications
are scheme-theoretically dense and every subsequent center is supported
away from the preserved copy of $U$. The asserted quasi-compactness and
density follow.
