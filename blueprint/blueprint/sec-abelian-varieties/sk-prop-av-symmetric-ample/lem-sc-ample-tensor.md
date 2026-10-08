+++
id = "lem-sc-ample-tensor"
kind = "lemma"
title = "Tensor products of ample modules"
lean = ["AlgebraicGeometry.IsAbelianScheme.isAmple_symmetrisation", "AlgebraicGeometry.IsAbelianScheme.nonempty_iso_overPullback_inv_symmetrisation"]
order = 478
uses = ["def-sc-abelian-variety", "def-sc-ample", "lem-chow-segre"]
+++
Let $X$ be a scheme over a field $k$ and let $\mathcal L$ and
$\mathcal M$ be ample invertible
$\mathcal O_X$-modules. Then $\mathcal L\otimes\mathcal M$ is
ample. In particular, for an
abelian variety $A$ and an
ample invertible module $\mathcal L$ on $A$, the module
$\mathcal L\otimes[-1]^*\mathcal L$ is ample and satisfies
$[-1]^*(\mathcal L\otimes[-1]^*\mathcal L)\cong\mathcal L\otimes [-1]^*\mathcal L$.

## Proof

*Reference: Stacks Project, Properties of Schemes, Lemma
28.27.5, [Tag 0890](https://stacks.math.columbia.edu/tag/0890).*
Choose $a,b\geq1$ with $\mathcal L^{\otimes a}$ and
$\mathcal M^{\otimes b}$ very ample; then
$(\mathcal L\otimes\mathcal M)^{\otimes ab}$ is very ample: the
tensor product of very ample modules is very ample, being the
pullback of $\mathcal O(1)\boxtimes\mathcal O(1)$ along the Segre
embedding ([lem-chow-segre]). Hence
$\mathcal L\otimes\mathcal M$ is ample. For the second part,
$[-1]$ is an automorphism of $A$, so $[-1]^*\mathcal L$ is
ample and $[-1]^*[-1]^*\mathcal L\cong\mathcal L$; therefore
$[-1]^*(\mathcal L\otimes[-1]^*\mathcal L)\cong[-1]^*\mathcal L\otimes\mathcal L\cong\mathcal L\otimes[-1]^*\mathcal L$.
