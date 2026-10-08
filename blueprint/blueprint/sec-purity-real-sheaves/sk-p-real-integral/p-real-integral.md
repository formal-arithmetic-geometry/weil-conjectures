+++
id = "p-real-integral"
kind = "theorem"
title = "Integral models"
order = 2596
uses = ["def-wf-fundamental-representation", "lem-wf-weil-fundamental-representation", "lem-wf-weil-group-exact-sequence", "prop-wf-weil-sheaf-representation-equivalence"]
tags = ["latex:proposition"]
+++
Keep the notation of [prop-wf-weil-sheaf-representation-equivalence], and let $U_0\subseteq C_0$ be a
nonempty open subscheme with base change $U$ and geometric fundamental group
$\pi_1(U)$, the kernel of the degree map of $W(U_0)$ by
[lem-wf-weil-group-exact-sequence]. An $\mathcal O_E$-lattice in $V$ means a free
$\mathcal O_E$-submodule of rank $\dim_{E}V$ that spans $V$ over $E$.

Let $(V,\rho)$ be a lisse Weil sheaf on $U_0$, with $\rho$ its Weil
fundamental representation of [def-wf-fundamental-representation]. After replacing $E$ by a
finite extension there is an $\mathcal O_E$-lattice $L\subset V$ with

$$
\rho(\pi_1(U))L=L,\qquad L\otimes_{\mathcal O_E}E=V,
$$

and the image of $\pi_1(U)$ in $\operatorname{Aut}(L/\mathfrak m_E^nL)$ is
finite for every $n$. Such an $L$ is the geometric stalk of a lisse
$\mathcal O_E$-sheaf on $U$.

## Proof

By [prop-wf-weil-sheaf-representation-equivalence] the representation admits a model over a finite
$E/\Ql$, whose restriction to the geometric subgroup is continuous by
[lem-wf-weil-fundamental-representation]; a further
finite extension absorbs that choice. Since $\pi_1(U)$ is profinite, hence
compact, $\rho(\pi_1(U))$ is a compact subgroup of $\GL(V)$. The orbit of an
arbitrary $\mathcal O_E$-lattice under a compact subgroup is bounded, so the
$\mathcal O_E$-span $L$ of that orbit is again a lattice; it is stable by
construction and of full rank, whence $L\otimes_{\mathcal O_E}E=V$. Each
$L/\mathfrak m_E^nL$ is a finite set, so the image of $\pi_1(U)$ in its
automorphisms is finite, and these reductions form the compatible system of
finite locally constant sheaves whose limit is the lisse $\mathcal O_E$-sheaf
on $U$ with stalk $L$.

Uses: [def-wf-fundamental-representation], [lem-wf-weil-fundamental-representation], [lem-wf-weil-group-exact-sequence], [prop-wf-weil-sheaf-representation-equivalence]
