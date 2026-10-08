+++
id = "lemma-weil-pbc-projection-formula-compactified"
kind = "lemma"
title = "Compactified finite-level projection formula"
order = 1271
uses = ["lemma-weil-pbc-projection-formula-open-piece", "lemma-weil-pbc-projection-formula-proper-piece"]
+++
For a chosen compactification and a perfect $Q$ on $Y$, the ordered composite

$$
\begin{aligned}
(Rf_!^{(j,p)}E)\otimes^LQ
&=(Rp_*j_!E)\otimes^LQ\\
&\xrightarrow{\pi_{p,j_!E,Q}}
Rp_*(j_!E\otimes^LLp^*Q)\\
&\xrightarrow{Rp_*\theta_j}
Rp_*j_!(E\otimes^LLf^*Q)
=Rf_!^{(j,p)}(E\otimes^LLf^*Q)
\end{aligned}
$$

is an isomorphism. Here $\theta_j$ is the open-piece isomorphism and the
inverse is $\rho_{p,j_!E,Q}\,Rp_*(\theta_j^{-1})$ in reverse order.

## Proof

The assertion is local on $Y$. On a cover choose a strict-perfect package
for $Q$. The first arrow and its displayed inverse are the proper-piece
inverse pair. The second arrow and its inverse come from the open-piece
inverse pair, using
$Lj^*Lp^*Q=Lf^*Q$. Associativity gives

$$
\rho_{p,j_!E,Q}(Rp_*\theta_j^{-1})
(Rp_*\theta_j)\pi_{p,j_!E,Q}=1
$$

and

$$
(Rp_*\theta_j)\pi_{p,j_!E,Q}
\rho_{p,j_!E,Q}(Rp_*\theta_j^{-1})=1.
$$

These are precisely the two inverse equations for the ordered composite.
They prove that the globally defined forward map is an isomorphism; uniqueness
of an inverse glues the local reverse maps.
