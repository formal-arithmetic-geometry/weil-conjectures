+++
id = "lemma-nagata-compactification-base-change"
kind = "lemma"
title = "Base change of a compactification"
order = 76
lean = ["AlgebraicGeometry.HasCompactification.of_isPullback"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-compactification-base-change"]
+++
The constructed factorization $C_{S'}$ is a compactification of
$X\times_SS'\to S'$.

## Proof

Open immersions, quasi-compact morphisms, and proper morphisms are stable
under arbitrary base change. The factorization equality follows from the
universal property of the two fibre products.
