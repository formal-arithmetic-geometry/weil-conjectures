+++
id = "lem-weil-pbc-finite-reduction-reconstruction"
kind = "lemma"
title = "Finite reduction of reconstruction"
order = 1249
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "prop-weil-pbc-koszul-reconstruction", "prop-weil-pbc-roos-triangle"]
+++
For every $a\geq1$, the derived counit from inverse limit to evaluation
induces a functorial isomorphism

$$
 (\Rlim K_\bullet)\otimes_A^LP_a\xrightarrow{\sim}K_a.
$$

Moreover, $(-)\otimes_A^LP_a$ commutes with the two derived countable
products occurring in the Roos triangle attached to the derived inverse-limit
construction.

(*Source note:* the reduction isomorphism is the finite-level form of derived
completeness in Stacks Project, Lemma 61.20.1 (Tag
[099M](https://stacks.math.columbia.edu/tag/099M):
$K=\Rlim(K\otimes^L_\Lambda\underline{\Lambda/I^n})$ for a derived complete
$K$, for a Noetherian ring $\Lambda$ with an ideal $I$ on an arbitrary site)
and of the Koszul form of Lemma 15.93.17 (Tag
[091Z](https://stacks.math.columbia.edu/tag/091Z): $K$ is derived complete if
and only if $K\to\Rlim(K\otimes_A^{\mathbf L}K_n^\bullet)$ is an
isomorphism). Those entries concern a single derived complete object of
$D(\mathcal C,\Lambda)$; the form used here is tower-level, being stated for
the strict quotient tower of [def-weil-pbc-adic-coefficient-datum], and it
adds the commutation of $(-)\otimes_A^LP_a$ with the two derived products of
the Roos triangle, which the verified entries do not state.)

## Proof

By [prop-weil-pbc-koszul-reconstruction] the Koszul completion is identified
with $\Rlim K_\bullet$, so we verify the statement for the Koszul completion:
tensoring the strict Koszul tower with the bounded finite-projective
representative of $P_a$ and evaluating at the $a$-th stage gives the
canonical isomorphism. The commutation with the two derived products is the
compatibility of tensor with products in the Roos triangle of
[prop-weil-pbc-roos-triangle].
