+++
id = "sk-p-real-operations"
kind = "section"
title = "Local Frobenius polynomials"
order = 2590
uses = ["sec-algebraic-groups-lie-algebras", "sec-poincare-duality", "sk-d-real-operations", "sk-d-real-weights", "sk-d-real-weil", "sk-i-real-sheaves"]
lean = ["AlgebraicGeometry.WeilGroup.localPolynomial_eq_charpolyRev_of_isConj"]
+++
*Proposition (sketch).*

Keep the notation of [sk-i-real-sheaves], and let $x$ be a closed point of
$C_0$ of degree $e_x$, with local Frobenius $F_x$ acting on the stalk
$\mathcal F_{\bar x}$; by [sk-d-real-weil] it acts through the
conjugacy class in $W(C_0)$ of geometric Frobenius elements at $x$,
which have degree $e_x$. Use the tensor equivalence of
[sk-i-real-sheaves] for the operations of [sk-d-real-operations], and
write $P_x$ for the local characteristic polynomial of
[sk-d-real-weights]. Then

$$
P_x(\mathcal F,T)=\det\bigl(1-T\,\rho(F_x)\mid V\bigr)
\qquad\text{for every closed }x .
$$

## Proof

Granted [sk-i-real-sheaves], the operations of [sk-d-real-operations] on
lisse Weil sheaves are *defined* by transport along the equivalence, so
only the local polynomial needs an argument. Iterating the Frobenius
structure map $e_x$ times on the stalk at $\bar x$ realizes $F_x$ as $\rho$ of
any member of the degree-$e_x$ class supplied by $x$. A characteristic
polynomial is invariant under conjugation, so $\det(1-T\rho(F_x)\mid V)$ is
independent of the member chosen and agrees with the stalkwise $P_x$ of
[sk-d-real-weights].

Uses: [sk-d-real-operations], [sk-d-real-weights], [sk-d-real-weil], [sk-i-real-sheaves]
