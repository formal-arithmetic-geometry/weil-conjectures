+++
id = "sk-d-tangent"
kind = "section"
title = "Tangent spaces and rational actions"
order = 2480
uses = ["sk-d-geometry", "sk-d-lie"]
lean = ["AlgebraicGeometry.tangentGroup", "Matrix.GeneralLinearGroup.lieAlgebra", "Matrix.GeneralLinearGroup.RationalHom", "Matrix.GeneralLinearGroup.RationalHom.differential"]
+++
*Definition (sketch).*

For an affine variety $X$ and a $k$-point $x$,
let $\mathfrak m_x$ be the maximal ideal of functions vanishing at $x$.
The tangent space is $T_xX=(\mathfrak m_x/\mathfrak m_x^2)^\vee$.
A regular map induces a linear map on these spaces, its differential.
For a matrix group set $\Lie(G)=T_1G$; equivalently,
$X\in\Lie(G)$ when $1+\varepsilon X\in G(k[\varepsilon]/\varepsilon^2)$.
Here $R$-points mean matrices satisfying the defining equations over
the commutative $k$-algebra $R$. The bracket is $XY-YX$.
A rational representation is a regular homomorphism $r:G\to\GL(M)$;
its differential $dr$ is a Lie representation.
The adjoint action is $\operatorname{Ad}(g)X=gXg^{-1}$, with differential
$\operatorname{ad}(Y)X=[Y,X]$.

A finite-type matrix group scheme is a closed subscheme of $\GL(V)$,
cut out by a finitely generated ideal, possibly nonradical, such that
the regular group operations restrict to it. Its coordinate algebra
therefore need not initially be reduced. At a closed point, smoothness
over $k$ means that the dimension of the tangent space equals the
Krull dimension of the local ring; such a local ring is called regular.
The local ring is the localization of the coordinate algebra at the
point's maximal ideal.

Uses: [sk-d-geometry], [sk-d-lie]
