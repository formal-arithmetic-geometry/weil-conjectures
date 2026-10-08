+++
id = "sk-prop-av-deg-pullback"
kind = "section"
title = "Degree of a pullback under a finite morphism"
lean = ["AlgebraicGeometry.Scheme.Hom.degree_pullback"]
order = 483
uses = ["sk-def-av-ample-degree", "sk-def-av-pic"]
+++
*Proposition (sketch).*

Let $f:X\to Y$ be a finite surjective morphism of proper varieties of
dimension $g$ over a field $k$, let $\cM$ be an ample invertible
$\cO_Y$-module and let $\deg(f)=[k(X):k(Y)]$ be the degree of $f$.
Then

$$
\deg_{f^*\cM}(X)=\deg(f)\cdot\deg_{\cM}(Y),
$$

the degrees being those of [sk-def-av-ample-degree].

## Proof

By the projection formula $\chi(X,f^*\cM^{\otimes m}) =\chi(Y,f_*\cO_X\otimes\cM^{\otimes m})$. The coherent sheaf
$f_*\cO_X$ has generic rank $[k(X):k(Y)]=\deg(f)$, and for a coherent
$\mathcal E$ of generic rank $r$ on the proper $g$-dimensional $Y$ the
polynomial $m\mapsto\chi(Y,\mathcal E\otimes\cM^{\otimes m})$ has the
same leading coefficient as $r\cdot\chi(Y,\cM^{\otimes m})$ (additivity
of $\chi$ plus devissage reduces to $\mathcal E$ invertible, where the
two polynomials differ in degree $\le g-1$). Hence the leading
coefficients, and with them the degrees of [sk-def-av-ample-degree],
multiply by $\deg(f)$.

Uses: [sk-def-av-ample-degree]
