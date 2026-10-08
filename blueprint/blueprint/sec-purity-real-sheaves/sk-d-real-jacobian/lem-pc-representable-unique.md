+++
id = "lem-pc-representable-unique"
kind = "lemma"
title = "Uniqueness of the representing scheme"
order = 2608
uses = ["def-pc-scheme", "lem-pc-yoneda"]
+++
Let $S$ be a scheme and
$F:(\mathit{Sch}/S)^{\mathrm{op}}\to\textit{Sets}$ a functor. If $P$ and
$Q$ are schemes over $S$ with $h_P\cong F\cong h_Q$, then there is a
unique isomorphism $P\to Q$ over $S$ inducing the composite isomorphism.

## Proof

By [lem-pc-yoneda] the isomorphisms correspond to elements
$\xi\in F(P)$ and $\eta\in F(Q)$; the isomorphism
$h_P\cong h_Q$ corresponds under Yoneda to an element of $h_Q(P)$, i.e. a morphism $f:P\to Q$; from naturality, the assignment
$\tau\mapsto\tau_P(\mathrm{id}_P)$ sends the isomorphism to $f$; applying
Yoneda to the inverse isomorphism gives $g:Q\to P$; the composite
$g\circ f\in h_P(P)$ corresponds to the identity under the composed
isomorphism, hence $g\circ f=\mathrm{id}_P$ (Yoneda's injectivity on
$h_P(P)$); similarly $f\circ g=\mathrm{id}_Q$, so $f$ is an isomorphism; the
uniqueness is again the injectivity of Yoneda.
