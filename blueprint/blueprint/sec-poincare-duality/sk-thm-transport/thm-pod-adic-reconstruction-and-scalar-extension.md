+++
id = "thm-pod-adic-reconstruction-and-scalar-extension"
kind = "theorem"
title = "Adic reconstruction and scalar extension"
order = 2450
uses = ["def-pod-conventions", "def-pod-derived-poincare-pairing", "def-weil-pbc-adic-coefficient-datum", "lem-weil-pbc-reconstruction-uniform-tower", "thm-pod-derived-poincare-duality", "thm-pod-finite-reduction"]
+++
Let $X/k$ be smooth and geometrically connected as in
the Poincare duality conventions, and
let $K$ be a derived-complete
site-perfect $\mathcal O_E$-complex whose reductions
$K_n=K\otimes^L A_{E,n}$ form a normalized system with common
constructible and finite-Tor bounds. Assume the admissible structure
morphism and coefficient conventions used for the Poincare pairing. The finite-level pairings $\beta _{K_n}$ of Definition 9.17 form a morphism of normalized systems in the sense of Definition 2.148 (by Theorem 9.33), and they induce the $\mathcal O_E$-valued derived Poincare pairing

$$
R\Gamma _c(X,K)\otimes ^L_{\mathcal O_E}R\Gamma \bigl(X,K^\vee (d)\bigr)[2d] \longrightarrow \mathcal O_E,
$$

perfect in the sense of the uniform-tower reconstruction of Lemma 2.156: the inverse of its adjoint is the canonical isomorphism

$$
R\Gamma _c(X,K)^\vee \xrightarrow {\  \sim \  } R\Gamma \bigl(X,K^\vee (d)\bigr)[2d]
$$

over $\mathcal O_E$. Localization at $\varpi _E$ and finite coefficient-field extension carry this pairing, its adjoint, every degree-indexing map, the relative form, and all Frobenius squares to their counterparts over the extended coefficient field.

## Proof

By [thm-pod-finite-reduction], the reduction of the inverse adjoint $\beta _{K_{n+1}}^\sharp$ along $A_{E,n+1}\to A_{E,n}$ is $\beta _{K_n}^\sharp$, so the finite-level inverse adjoints form a morphism of normalized systems with the common bounds and amplitudes inherited from $K$; the realization under the uniform-tower reconstruction of [lem-weil-pbc-reconstruction-uniform-tower] is the displayed $\mathcal O_E$-level inverse adjoint, whose levelwise perfectness is [thm-pod-derived-poincare-duality] (the perfectness and the pairing over $\mathcal O_E$ are then the corresponding statements over the realized object). Scalar extension to $E$ and to a finite coefficient field is the exactness of the extension functors, and transport along the finite-reduction and scalar-extension rectangles of [thm-pod-finite-reduction] gives the compatibility of the pairing, the adjoint, the degree-indexing maps, and the Frobenius squares.
