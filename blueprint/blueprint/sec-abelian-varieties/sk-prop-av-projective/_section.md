+++
id = "sk-prop-av-projective"
kind = "section"
title = "Abelian varieties are projective"
lean = ["AlgebraicGeometry.IsAbelianScheme.exists_isClosedImmersion_projectiveSpace", "AlgebraicGeometry.IsAbelianScheme.exists_isAmple"]
order = 473
uses = ["sk-def-av", "sk-def-av-ample-degree"]
+++
*Proposition (sketch).*

Every abelian variety $A$ over a field $k$ is projective over $k$; in
particular $A$ carries an ample invertible $\cO_A$-module.

## Proof

$A$ is an algebraic group scheme over $k$, hence quasi-projective
(`0BF7`); it is proper by [sk-def-av], and a quasi-projective
proper scheme over a field is projective (`0B45`, applied with
$S=\Spec k$). A projective scheme carries an ample module, namely the
pullback of $\cO(1)$ under the closed immersion into projective space
([sk-def-av-ample-degree]).

Uses: [sk-def-av-ample-degree], [sk-def-av]
