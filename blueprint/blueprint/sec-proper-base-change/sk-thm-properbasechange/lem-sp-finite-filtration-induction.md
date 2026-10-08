+++
id = "lem-sp-finite-filtration-induction"
kind = "lemma"
title = "Finite filtration induction"
order = 1209
uses = ["def-sp-filtration"]
+++
Let $(A,F)$ and $(A',F')$ be filtered objects [def-sp-filtration] with finite
filtrations, and let $\varphi:A\to A'$ be a morphism of filtered objects. If
$\operatorname{gr}^p\varphi$ is an isomorphism for all $p$, then $\varphi$ is
an isomorphism.

## Proof

Apply the five lemma to the commutative diagram of short exact sequences

$$
\begin{array}{ccccccccc}
0&\to& F^{p+1}A&\to& F^{p}A&\to& \operatorname{gr}^p A&\to&0\\
&&\downarrow&&\downarrow&&\downarrow&&\\
0&\to& F^{p+1}A'&\to& F^{p}A'&\to& \operatorname{gr}^p A'&\to&0
\end{array}
$$

in which the third vertical arrow is an isomorphism by hypothesis: descending
induction on $p$, starting where both filtrations vanish (using the *graded
pieces* of [def-sp-filtration]) shows $F^{p}A\to F^{p}A'$ is an isomorphism
for all $p$, and $p=0$ gives the claim.
