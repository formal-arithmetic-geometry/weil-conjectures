+++
id = "lemma-nagata-rees-piece-mul"
kind = "lemma"
title = "Multiplication of Rees pieces"
order = 17
lean = ["AlgebraicGeometry.reesGrading.instGradedMonoid"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-piece-membership"]
+++
Multiplication maps

$$
\mathcal R_A(I)_m\cdot\mathcal R_A(I)_n
\subseteq\mathcal R_A(I)_{m+n}.
$$

## Proof

Write the two elements as $at^m$ and $bt^n$ with $a\in I^m$ and
$b\in I^n$. Their product is $(ab)t^{m+n}$ and
$ab\in I^mI^n=I^{m+n}$.
