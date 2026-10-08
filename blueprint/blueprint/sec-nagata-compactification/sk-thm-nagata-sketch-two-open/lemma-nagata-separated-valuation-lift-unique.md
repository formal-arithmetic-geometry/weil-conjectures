+++
id = "lemma-nagata-separated-valuation-lift-unique"
kind = "lemma"
title = "Uniqueness of a valuation lift for a separated morphism"
order = 296
lean = ["AlgebraicGeometry.IsSeparated.valuativeCriterion"]
+++
Let $f\colon Y\to S$ be separated, let $A$ be a valuation ring with
fraction field $K$, and let $h_1,h_2\colon\operatorname{Spec}(A)\to Y$ be
$S$-morphisms whose restrictions to $\operatorname{Spec}(K)$ coincide.
Then $h_1=h_2$.

## Proof

The equalizer of $h_1$ and $h_2$ is the inverse image of the diagonal
$\Delta_f\colon Y\hookrightarrow Y\times_S Y$. Since $f$ is separated,
this is a closed subscheme of $\operatorname{Spec}(A)$. It contains the
generic point because the two restrictions to $\operatorname{Spec}(K)$ are
equal. A valuation ring is a domain, so its generic point is the prime
$(0)$, whose closure is all of $\operatorname{Spec}(A)$. Hence the closed
equalizer is the whole spectrum, and the two morphisms are equal.
