+++
id = "lemma-constructible-pullback-finite"
kind = "lemma"
title = "Pullback of finite sheaves"
order = 1163
lean = ["AlgebraicGeometry.Scheme.IsFiniteSheaf.upperStar"]
uses = ["def-constructible-finite", "def-kun-separably-closed", "lemma-openclosed-stalk-upperstar"]
+++
Let $g\colon Y\to X$ be a morphism and let $\mathcal F\in\shv{\et X}$ be
finite. Then $g^*\mathcal F$ is finite.

## Proof

For a geometric point $\bar y$ of $Y$, the stalk $(g^*\mathcal F)_{\bar y}$
is the stalk $\mathcal F_{g\circ\bar y}$ by
[lemma-openclosed-stalk-upperstar], which is finite by hypothesis.
