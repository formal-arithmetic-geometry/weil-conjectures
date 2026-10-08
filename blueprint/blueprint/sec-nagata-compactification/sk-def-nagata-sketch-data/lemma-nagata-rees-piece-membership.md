+++
id = "lemma-nagata-rees-piece-membership"
kind = "lemma"
title = "Membership in one Rees piece"
order = 16
lean = ["AlgebraicGeometry.mem_reesGrading_iff_exists"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece"]
+++
An element $F\in\mathcal R_A(I)$ lies in $\mathcal R_A(I)_n$ if and only if
there is $a\in I^n$ such that the underlying polynomial of $F$ is
$at^n$.

## Proof

If $F$ is supported in degree $n$, coefficient extensionality gives
$F=\operatorname{monomial}(n,F_n)$. Membership in the Rees algebra gives
$F_n\in I^n$. Conversely, if the underlying polynomial is $at^n$ with $a\in I^n$, its
support is the singleton degree $n$ and the coefficient lies in the required
piece, so the defining membership condition for
$\mathcal R_A(I)_n$ holds.
