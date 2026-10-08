+++
id = "def-nagata-rees-algebra"
kind = "definition"
title = "Rees algebra"
order = 14
lean = ["reesAlgebra"]
+++
Let $A$ be a ring and $I\subseteq A$ an ideal. The Rees algebra is

$$
\mathcal R_A(I)=\bigoplus_{n\geq 0}I^nt^n\subseteq A[t].
$$

Its underlying ring is the subring of $A[t]$ consisting of polynomials whose
coefficient of $t^n$ belongs to $I^n$.

*Implementation note.* The current Mathlib object is the subalgebra
`reesAlgebra I` of the polynomial ring. The declarations
`mem_reesAlgebra_iff`, `reesAlgebra.monomial_mem`,
`adjoin_monomial_eq_reesAlgebra`, and
`reesAlgebra.fg` provide the membership and finite-generation facts
used below. The grading and the pieces in the next blocks are blueprint
data and must be defined explicitly.
