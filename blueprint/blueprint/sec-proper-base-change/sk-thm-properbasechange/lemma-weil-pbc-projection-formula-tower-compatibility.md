+++
id = "lemma-weil-pbc-projection-formula-tower-compatibility"
kind = "lemma"
title = "Projection formulas form a coefficient tower"
order = 1273
uses = ["def-weil-pbc-complete-coefficient-datum", "def-weil-pbc-projection-formula-arrows"]
+++
For every $n$, let $q_n:P_{n+1}\to P_n$ be the quotient. The square

$$
\begin{CD}
(Rf_*K)\otimes^LP_{n+1} @>{\pi_{n+1}}>>
Rf_*(K\otimes^LP_{n+1})\\
@V{1\otimes q_n}VV @VV{Rf_*(1\otimes q_n)}V\\
(Rf_*K)\otimes^LP_n @>{\pi_n}>> Rf_*(K\otimes^LP_n)
\end{CD}
$$

commutes, and so does the square with every $\pi$ replaced by $\rho$ and
horizontal arrows reversed; its vertical arrows remain the two quotient
maps.

## Proof

The two adjoints of the forward composites are both

$$
Lf^*Rf_*K\otimes^LP_{n+1}
\xrightarrow{\epsilon_K\otimes1}K\otimes^LP_{n+1}
\xrightarrow{1\otimes q_n}K\otimes^LP_n.
$$

Thus the forward square commutes. Invert the two horizontal isomorphisms in
the equality
$Rf_*(1\otimes q_n)\pi_{n+1}=\pi_n(1\otimes q_n)$ to obtain the asserted
compatibility for $\rho$.
