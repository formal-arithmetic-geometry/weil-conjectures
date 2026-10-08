+++
id = "lem-pc-affine-vanishing"
kind = "lemma"
title = "Vanishing of cohomology on affine schemes"
order = 608
uses = ["def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-cech-complex"]
lean = ["AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine"]
+++
Let $X=\operatorname{Spec}(A)$ be an affine scheme and $\mathcal{F}$ a quasi-coherent
$\mathcal{O}_X$-module. Then $H^p(X,\mathcal{F})=0$ for all $p>0$.

## Proof

Apply the standard Cech criterion (Stacks Project, Cohomology,
Lemma 20.11.9; the section is Cohomology, Section 20.11, Tag
[01EO](https://stacks.math.columbia.edu/tag/01EO)): let
$\mathcal B$ be the basis of affine opens of $X$ and $\mathrm{Cov}$ the
set of the standard coverings $\{D(f_i)\}$ of affine opens; then
(1) the generating open subsets are closed under finite intersections
(the product of localization maps of $D(f_1\cdots f_m)$-type: the
intersection of standard opens is a standard open), (2) the system
$\mathrm{Cov}$ is cofinal in the coverings of the sets $V\in\mathcal B$
by members of $\mathcal B$ (every open of an affine is a union of
standard opens, and $\operatorname{Spec} A$ is quasi-compact, so every affine open
has a finite standard subcovering; Schemes, Section 26.5), and
(3) for $V\in\mathcal B$ and $\{V_i\to V\}\in\mathrm{Cov}$, the
augmented Cech complex with values in $\mathcal{F}|_V$ is exact in positive
degrees ([lem-pc-affine-cech-complex] with $M=\mathcal{F}(V)$). The
criterion then gives $H^p(X,\mathcal{F})=0$ for $p>0$.
