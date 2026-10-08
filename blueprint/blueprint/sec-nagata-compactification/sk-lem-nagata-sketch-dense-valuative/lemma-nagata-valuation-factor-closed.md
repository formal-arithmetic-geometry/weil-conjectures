+++
id = "lemma-nagata-valuation-factor-closed"
kind = "lemma"
title = "Factorization through a closed subscheme over a valuation ring"
order = 277
lean = ["AlgebraicGeometry.IsClosedImmersion.exists_lift_of_isFractionRing"]
uses = ["def-nagata-dense-compactification", "def-nagata-scheme-image-comparison", "lemma-nagata-reduced-dense-image-schematic", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal"]
+++
Let $A$ be a valuation ring with fraction field $K$, let $Z\hookrightarrow Y$
be a closed immersion, and let $g\colon\operatorname{Spec}(A)\to Y$. If the
restriction of $g$ to $\operatorname{Spec}(K)$ factors through $Z$, then
$g$ factors through $Z$.

## Proof

Pull the defining ideal of $Z$ back to $A$. It becomes zero after applying
the injective map $A\hookrightarrow K$, so it was already zero in $A$.
