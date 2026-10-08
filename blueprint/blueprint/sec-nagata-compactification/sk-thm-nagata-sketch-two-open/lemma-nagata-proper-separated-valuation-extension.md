+++
id = "lemma-nagata-proper-separated-valuation-extension"
kind = "lemma"
title = "Valuative extension to a proper separated morphism"
order = 297
lean = ["AlgebraicGeometry.IsProper.eq_valuativeCriterion"]
uses = ["lemma-nagata-proper-valuative-criterion-existence-api", "lemma-nagata-separated-valuation-lift-unique"]
+++
Let $f\colon Y\to S$ be proper and separated. Every commutative square

$$
\operatorname{Spec}(K)\longrightarrow Y
\qquad\text{over}\qquad
\operatorname{Spec}(A)\longrightarrow S
$$

with $A$ a valuation ring and $K=\operatorname{Frac}(A)$ admits a unique
lift $\operatorname{Spec}(A)\to Y$.

## Proof

Existence is the output of
[lemma-nagata-proper-valuative-criterion-existence-api]. If $h$ and
$h'$ are two such lifts, their generic restrictions are the prescribed
morphism, so
[lemma-nagata-separated-valuation-lift-unique] gives $h=h'$. Thus the
extension exists and is unique.
