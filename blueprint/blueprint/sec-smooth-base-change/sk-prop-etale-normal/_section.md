+++
id = "sk-prop-etale-normal"
kind = "section"
title = "Étale covers of a normal scheme with separably closed function field"
order = 1402
uses = ["sk-def-smooth"]
lean = ["AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField", "AlgebraicGeometry.Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField"]
+++
*Proposition (sketch).*

Let $S$ be an integral normal scheme whose function field
$L=\kappa(\eta)$ is separably closed, and let $V\to S$ be separated
and étale. Then $V$ is a disjoint union of open subschemes of $S$
— finitely many as soon as $V$ is quasi-compact.
(Stacks Project, Lemma 59.80.4, Tag `09Z9`.)

## Proof

Being étale over a normal scheme, $V$ is normal, so its connected
components $V_i$ are integral; being étale, $V\to S$ is open, and
every nonempty open of the irreducible $S$ is dense, so each $V_i$
dominates $S$. The generic fibre $V_\eta$ is étale over $\Spec L$
with $L$ separably closed, hence a disjoint union of copies of
$\Spec L$; therefore each $V_i$ has function field $L$, i.e. $V_i\to S$ is birational. A separated quasi-finite $V_i\to S$
factors by Zariski's main theorem as an open immersion
$V_i\hookrightarrow W$ followed by a finite $\pi:W\to S$, and $W$ may
be taken integral with function field $L$; then
$\mathcal O_S\subseteq\pi_*\mathcal O_W\subseteq L$ is an integral
extension, so $\pi_*\mathcal O_W=\mathcal O_S$ by normality of $S$
and $\pi$ is an isomorphism. Hence each $V_i\to S$ is an open
immersion. If moreover $V$ is quasi-compact then $V_\eta$ is finite,
so there are finitely many $V_i$.

Uses: [sk-def-smooth]
