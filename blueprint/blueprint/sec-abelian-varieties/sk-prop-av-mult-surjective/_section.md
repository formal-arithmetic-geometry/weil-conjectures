+++
id = "sk-prop-av-mult-surjective"
kind = "section"
title = "Surjectivity of the multiplication map"
lean = ["AlgebraicGeometry.surjective_npow_id"]
order = 553
uses = ["sk-cor-av-commutative", "sk-def-av", "sk-def-av-mult-n", "sk-prop-av-char", "sk-prop-av-mult-finite", "sk-prop-av-mult-hom"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety of dimension $g$ over $k$ and $n\ge1$.
Then $[n]:A\to A$ is surjective, so $A$ is a divisible group scheme
and $\dim A[n]=0$.

## Proof

The image $H:=[n](A)$ is a closed subgroup scheme of $A$: it is the
image of a homomorphism from the proper $A$ to the separated finite
type $A$, hence closed, and it is a subgroup scheme (blueprint
lem:sc-image-subgroup). Since $[n]$ is finite
([sk-prop-av-mult-finite]) its fibres are zero-dimensional, so the
dimension formula for a surjective morphism of varieties of finite
type over a field gives
$\dim H=\dim A-\dim A[n]=\dim A$. Now $A$ is irreducible
([sk-prop-av-char]) and $H\subseteq A$ is closed of full dimension,
so $H_{\mathrm{red}}=A$ and hence $H=A$.

Uses: [sk-cor-av-commutative], [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-char], [sk-prop-av-mult-finite], [sk-prop-av-mult-hom]
