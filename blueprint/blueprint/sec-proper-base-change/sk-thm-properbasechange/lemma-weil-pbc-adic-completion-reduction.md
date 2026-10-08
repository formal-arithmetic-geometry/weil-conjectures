+++
id = "lemma-weil-pbc-adic-completion-reduction"
kind = "lemma"
title = "Finite reduction of adic completion"
order = 1260
uses = ["lemma-weil-pbc-koszul-quotient-limit"]
+++
For every $a\geq1$, projection to level $a$ induces a functorial
isomorphism

$$
\left(R\varprojlim_nK_n\right)\otimes^L_\Lambda P_a
\xrightarrow{\sim}K_a.
$$

## Proof

Use the preceding comparison to replace the quotient tower by
$K\otimes^LQ_m$. Since $P_a$ is perfect, tensoring with $P_a$ commutes
with both products in the product-cone model. For $m\geq a$, the
differential of $Q_m\otimes^L P_a$ is zero. Its degree-zero transition is
the identity, whereas every composite of $a$ successive transitions in a
negative degree contains a factor $f_j^a\in I^a$ and is zero over $P_a$.
Thus the negative-degree towers are pro-zero and the degree-zero tower is
the constant tower $P_a$. After tensoring with $K$, its product-cone limit
is $K\otimes^LP_a=K_a$. The surviving degree-zero projection is precisely
the displayed map. This also exposes the finite Tor-amplitude input: the
bounded finite-projective complex representing $P_a$ is what permits it to
pass through the two countable products.
