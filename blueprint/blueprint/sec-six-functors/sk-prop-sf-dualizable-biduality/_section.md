+++
id = "sk-prop-sf-dualizable-biduality"
kind = "section"
title = "Biduality of a perfect complex"
order = 2172
uses = ["sk-def-sf-operations"]
lean = ["AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual", "AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual", "AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor"]
+++
*Proposition (sketch).*

Let $K\in\Dctf(X,\Lambda)$ be quasi-isomorphic, locally on the site of $X$, to
a bounded complex of finite projective $\Lambda_X$-modules. Then
$K^\vee=\RHom_X(K,\Lambda_X)$ is perfect, the evaluation
$K\otimes^L_{\Lambda_X}K^\vee\to\Lambda_X$ is defined, and $K\to K^{\vee\vee}$
is an isomorphism, evaluation and coevaluation being the unit and counit of
the tensor–internal-Hom adjunction. For every $M\in\Dctf(X,\Lambda)$ the
canonical map $K^\vee\otimes^L_{\Lambda_X}M\to\RHom_X(K,M)$ is an isomorphism.

## Proof

For $P$ finite projective the canonical maps
$P^\vee\otimes^LN\to\RHom_X(P,N)$ and $P\to P^{\vee\vee}$ are isomorphisms:
true for $P=\Lambda_X^r$ by inspection, and both constructions are exact
functors of $P$ preserving direct summands, so they hold for a projective $P$,
which is locally a direct summand of a finite free module. Applying this
termwise to a bounded complex of finite projectives representing $K$ gives
$K^{\vee\vee}\cong K$; the counit and coevaluation are the adjunction unit and
counit, whose composite is the identity.

Uses: `\Cref{sk-def-sf-operations}`, `def-weil-derived-pullback-tensor-hom`
