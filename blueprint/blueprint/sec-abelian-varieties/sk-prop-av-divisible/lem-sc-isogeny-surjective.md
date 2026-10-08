+++
id = "lem-sc-isogeny-surjective"
kind = "lemma"
title = "Surjectivity of the multiplication map on points"
lean = ["AlgebraicGeometry.surjective_npow_points"]
order = 572
uses = ["def-sc-abelian-variety", "def-sc-mult-n", "lem-sc-finite-flat-surj-points", "lem-sc-isogeny-facts"]
+++
Let $A$ be an abelian variety
over an algebraically closed field $k$ and let $n\geq1$. Then

$$
[n]:A(k)\longrightarrow A(k)
$$

is surjective.

## Proof

By [lem-sc-isogeny-facts](a), $[n]$ is a finite flat
surjective morphism, so it is surjective on $k$-points by
[lem-sc-finite-flat-surj-points]
(*reference: Stacks Project, Groupoid Schemes, Proposition
39.9.11, parts (3) and (4), [Tag 03RP](https://stacks.math.columbia.edu/tag/03RP): $[n]$ is surjective, and
$A(k)$ is divisible for $k$ algebraically closed*).
