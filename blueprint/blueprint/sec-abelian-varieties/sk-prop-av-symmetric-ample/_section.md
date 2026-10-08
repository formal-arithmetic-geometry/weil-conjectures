+++
id = "sk-prop-av-symmetric-ample"
kind = "section"
title = "A symmetric ample module"
lean = ["AlgebraicGeometry.IsAbelianScheme.isAmple_symmetrisation", "AlgebraicGeometry.IsAbelianScheme.nonempty_iso_overPullback_inv_symmetrisation"]
order = 475
uses = ["sk-def-av", "sk-def-av-ample-degree", "sk-prop-av-projective"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety over $k$ and let $\cL$ be an ample
invertible $\cO_A$-module. Then

$$
\cN:=\cL\otimes[-1]^*\cL
$$

is ample and *symmetric*: $[-1]^*\cN\cong\cN$.

## Proof

As $[-1]$ is an automorphism of $A$, $[-1]^*\cL$ is ample. A tensor
product of two ample modules is ample: choose $a,b\ge1$ with
$\cL^{\otimes a}$ and $([-1]^*\cL)^{\otimes b}$ very ample, so that
$\cL^{\otimes ab}$ and $([-1]^*\cL)^{\otimes ab}$ are both very ample;
then $\cN^{\otimes ab}=\cL^{\otimes ab}\otimes([-1]^*\cL)^{\otimes ab}$
is very ample, being the pullback of $\cO(1)\boxtimes\cO(1)$ along the
Segre embedding composed with the product of the two projective
embeddings, so $\cN=\cL\otimes[-1]^*\cL$ is ample. Finally
$[-1]^*[-1]^*\cL\cong\cL$, whence
$[-1]^*\cN\cong[-1]^*\cL\otimes\cL\cong\cN$.

Uses: [sk-def-av-ample-degree], [sk-def-av], [sk-prop-av-projective]
