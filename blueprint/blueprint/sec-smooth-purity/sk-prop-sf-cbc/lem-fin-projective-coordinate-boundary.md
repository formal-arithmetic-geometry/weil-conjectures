+++
id = "lem-fin-projective-coordinate-boundary"
kind = "lemma"
title = "A projective coordinate complement is finite"
order = 1634
uses = ["def-weil-pbc-scheme-conventions", "lem-fin-projective-finite-fibres"]
+++
Let $S=\operatorname{Spec}A$ be integral Noetherian and let
$Y\to S$ be projective. Choose a finite affine cover
$Y_\alpha\hookrightarrow\mathbf A^{m_\alpha}_S$, with
$m_\alpha\geq1$, and a dense open
$V_{\alpha r}\subset\mathbf A^1_S$ for each coordinate.
After restriction to a nonempty open of $S$, the reduced closed
complement $Z$ of
$\bigcup_{\alpha,r}t_{\alpha r}^{-1}(V_{\alpha r})$
is finite over $S$.
The notation refers to scheme conventions.

## Proof

The ideal defining $\mathbf A^1_S\setminus V_{\alpha r}$
contains a nonzero polynomial $P_{\alpha r}\in A[t]$.
Invert the finitely many nonzero leading coefficients and divide
by them, making these polynomials monic. On the reduced scheme
$Z\cap Y_\alpha$, every $P_{\alpha r}(t_{\alpha r})$
vanishes: it vanishes at all points and the coordinate ring is
reduced. Hence $Z\cap Y_\alpha$ is closed in

$$
\operatorname{Spec}
A[t_1,\ldots,t_{m_\alpha}]/
(P_{\alpha1}(t_1),\ldots,P_{\alpha m_\alpha}(t_{m_\alpha})).
$$

This algebra is finite over $A$, since products of powers below
the respective degrees generate it. Thus every geometric fiber
of every $Z\cap Y_\alpha$ has finitely many points.
The cover is finite, so the fibers of $Z\to S$ are finite.
As a closed subscheme of the projective $Y$, $Z$ is projective;
[lem-fin-projective-finite-fibres] proves finiteness.
