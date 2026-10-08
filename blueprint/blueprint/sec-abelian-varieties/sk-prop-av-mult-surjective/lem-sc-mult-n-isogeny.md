+++
id = "lem-sc-mult-n-isogeny"
kind = "lemma"
title = "Multiplication by $n$ is surjective with finite kernel"
lean = ["AlgebraicGeometry.surjective_npow_id"]
order = 555
uses = ["def-sc-abelian-variety", "def-sc-group-scheme", "def-sc-mult-n", "lem-sc-image-subgroup", "lem-sc-mult-n-finite-kernel", "lem-sc-mult-n-homomorphism"]
+++
Let $A$ be an abelian variety
over a field $k$, and let $n\geq1$. Then the map $[n]$ of
[def-sc-mult-n] is a surjective homomorphism of
group schemes, and its kernel
$A[n]$ is a finite group scheme over $k$.

## Proof

*Reference: Stacks Project, Groupoid Schemes, Proposition
39.9.11 (3) and (5), [Tag 03RP](https://stacks.math.columbia.edu/tag/03RP), whose proof is Lemma 39.9.8,
[Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG).*
By [lem-sc-mult-n-finite-kernel], $[n]$ is a finite homomorphism of group
schemes and its kernel $A[n]$ is a finite group scheme over $k$.

*Surjectivity.* The image $H:=[n](A)\subseteq A$ is a
closed subgroup scheme of $A$ by [lem-sc-image-subgroup] (the
source $A$ is proper over $k$ and the target $A$ is separated of
finite type over $k$), applied to the homomorphism $[n]$ of
[lem-sc-mult-n-homomorphism]. Since $[n]$ is finite, its fibres
have dimension zero, and the dimension formula for the surjective
morphism $A\to H$ gives
$\dim H=\dim A-\dim A[n]=\dim A$. Thus $H\subseteq A$ is a
closed subscheme of the irreducible scheme $A$ with
$\dim H=\dim A$; the reduced subscheme
$H_{\mathrm{red}}\subseteq A$ is then a closed subscheme of the
reduced irreducible scheme $A$ of the same dimension, hence
$H_{\mathrm{red}}=A$, and therefore $H=A$. So
$[n]:A\to A$ is surjective.
