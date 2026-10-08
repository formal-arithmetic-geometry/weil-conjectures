+++
id = "lemma-nagata-two-open-valuative-lifting"
kind = "lemma"
title = "Valuative lifting for the two-open candidate"
order = 303
lean = ["AlgebraicGeometry.HasCompactification.of_two_open_cover"]
uses = ["def-nagata-admissible-blowup", "def-nagata-common-modification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-global-blowup", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-compactification-candidate", "def-nagata-two-open-final-modification", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-blowup-proper", "lemma-nagata-boundary-loci", "lemma-nagata-common-modification", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-dense-source-valuative", "lemma-nagata-intermediate-separated", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-one-valuation-avoids-boundary", "lemma-nagata-proper-separated-valuation-extension", "lemma-nagata-proper-valuative-criterion-existence-api", "lemma-nagata-separated-valuation-lift-unique", "lemma-nagata-two-open-density-transport", "lemma-nagata-two-open-final-modification", "lemma-nagata-valuation-open-closed-point", "lemma-nagata-valuation-pair-factors-comparison", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
Let $A$ be a valuation ring with fraction field $K$. Every commutative
diagram whose generic map
$\operatorname{Spec}(K)\to W$ factors through $U_1\cap U_2$ has a unique
lift $\operatorname{Spec}(A)\to W$ over $S$.

## Proof

By
[lemma-nagata-proper-separated-valuation-extension], properness and
separatedness of $X_i\to S$ extend the generic map to maps
$g_i\colon\operatorname{Spec}(A)\to X_i$. By
[lemma-nagata-one-valuation-avoids-boundary], one extension factors
through $X_i\setminus\overline Z_{i,j}$ and hence through $W_i$. The
generic map already lifts to the preserved open $U\subseteq W'_i$.
The admissible blow-up $W'_i\to W_i$ is proper, hence separated, so
[lemma-nagata-proper-separated-valuation-extension] supplies a lift
to $W'_i$; its open map to $W$ gives the desired lift. Any two branch
choices have the same generic restriction. Since $W\to S$ is separated by
[lemma-nagata-two-open-final-modification],
[lemma-nagata-separated-valuation-lift-unique] makes the two maps
equal.
