+++
id = "lemma-nagata-admissible-blowup-over-open"
kind = "lemma"
title = "An admissible blow-up is unchanged over the preserved open"
order = 62
lean = ["AlgebraicGeometry.IsAdmissible.isIso_blowupMap_restrict"]
uses = ["def-nagata-admissible-blowup", "def-nagata-global-blowup", "lemma-nagata-affine-blowup-complement", "lemma-nagata-ideal-unit-off-support", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-complement"]
+++
If $\pi\colon X'\to X$ is $U$-admissible, then its center ideal restricts to
the unit ideal on $U$, and the induced morphism
$X'\times_XU\to U$ is an isomorphism. The inverse and the equality over
$U$ are part of the resulting specified isomorphism.

## Proof

Choose the ideal and blow-up identification from
[def-nagata-admissible-blowup]. The unit-ideal restriction is the
disjointness condition on the center. Apply
[thm-nagata-global-blowup-complement] to identify the blow-up over $U$
with $U$, then transport that isomorphism across the chosen identification
with $X'$.
