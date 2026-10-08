+++
id = "sk-prop-nagata-sketch-fp-models"
kind = "section"
title = "Finite-presentation models of a finite-type morphism"
order = 379
uses = ["sk-prop-nagata-sketch-approximation"]
lean = ["AlgebraicGeometry.Scheme.Hom.nonempty_finitePresentationApproximation"]
+++
*Proposition (sketch).*

Let $X,S$ be qcqs and let $X\to S$ be of finite type. There is
a system of finitely presented $S$-schemes $X_\alpha$ with closed
immersion transitions such that $X\simeq\varprojlim X_\alpha$;
each $X\to X_\alpha$ is a closed immersion.

## Proof

Finite affine-chart data first embeds $X$ into a finitely presented
$S$-scheme $Y$, after shrinking to a quasi-compact open in which the
immersion is closed. Write its ideal $\mathcal I$ as the filtered
union of finite-type quasi-coherent subideals $\mathcal I_\alpha$.
Then $X_\alpha=V(\mathcal I_\alpha)\subseteq Y$ has finite
presentation, and the quotient rings recover $X$ in the limit.
This is the model construction of 09ZQ.

Uses: [sk-prop-nagata-sketch-approximation]
