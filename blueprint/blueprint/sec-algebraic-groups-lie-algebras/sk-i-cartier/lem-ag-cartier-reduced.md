+++
id = "lem-ag-cartier-reduced"
kind = "lemma"
title = "Cartier: group schemes in characteristic zero are smooth and reduced"
order = 2492
uses = ["def-wf-lie-algebra-derivation", "lem-wf-affine-nullstellensatz-vanishing", "lem-wf-affine-product-reduced", "lem-wf-same-lie-closed-subgroup"]
lean = ["AlgebraicGeometry.isReduced_of_grpObj", "AlgebraicGeometry.smooth_of_grpObj_of_charZero", "Matrix.GeneralLinearGroup.lieAlgebra_identityComponent", "Matrix.GeneralLinearGroup.finrank_lieAlgebra_eq_ringKrullDim", "Matrix.GeneralLinearGroup.dualUnit_add"]
+++
Let $\mathcal G\subseteq\operatorname{GL}(V)$ over
$k=\overline{\mathbf Q}_\ell$ be a closed subscheme of finite type, cut
out by a finitely generated, possibly nonradical, ideal, such that the
multiplication and inversion of $\operatorname{GL}(V)$ restrict to it.
Then $\mathcal G$ is smooth and reduced, so
$\mathcal G=\mathcal G_{\mathrm{red}}$ is a (smooth) closed matrix group. In particular, if a closed subgroup (a
stabilizer, a centralizer, or the kernel of a regular homomorphism) is
given by explicit equations, its Lie algebra in the sense of
[def-wf-lie-algebra-derivation] is the space of $X$ such that
$1+\varepsilon X$ satisfies those equations over
$k[\varepsilon]/\varepsilon^2$; no passage to the reduced structure
changes the tangent space.

## Proof

*Reduction and smoothness of reduced groups.* The reduction
$\mathcal G_{\mathrm{red}}$ has the same $k$-points as $\mathcal G$, since
nilpotents die in $k$, and those points form a subgroup. Its
multiplication is defined on a product of reduced varieties, which is
reduced by [lem-wf-affine-product-reduced], so multiplication and
inversion factor through the reduction by the vanishing principle
([lem-wf-affine-nullstellensatz-vanishing]); thus $\mathcal G_{\mathrm{red}}$ is a reduced
closed matrix group. Such a group is smooth by (2) of
[lem-wf-same-lie-closed-subgroup].

*Cartier's step.* Write $A=k[\mathcal G]$, $N=\sqrt0$ and
$\mathfrak m=\mathfrak m_e$. Then $N\subseteq\mathfrak m^2$. Indeed, let
$b\in N$ be nonzero in $A_{\mathfrak m}$ with least nilpotence exponent
$n\ge2$ there, arranged so that $b^n=0$ in $A$. The counit identities
give $\Delta(b)=b\otimes1+1\otimes b+w$ with
$w\in\mathfrak m\otimes_k\mathfrak m$. Expanding $0=\Delta(b)^n$ modulo
$A\otimes\mathfrak m^2$ kills every term with two factors from
$1\otimes b+w$ and leaves
$nb^{n-1}\otimes b+n(b^{n-1}\otimes1)w=0$; passing further to
$A/(b^{n-1}\mathfrak m)$ in the first coordinate leaves
$n\,\overline{b^{n-1}}\otimes\overline b=0$ with both factors nonzero.
Since $n\ne0$ in characteristic zero, this is a contradiction, and the
degenerate case $b=0$ in $A_{\mathfrak m}$ gives $b\in\mathfrak m^2$
directly. Hence
$\mathfrak m/\mathfrak m^2\simeq(\mathfrak m/N)/(\mathfrak m/N)^2$, so
$\mathcal G$ and its reduction have the same cotangent space at $e$;
primes contain nilpotents, so they also have the same local dimension.
Smoothness of the reduction therefore makes the local ring of
$\mathcal G$ at $e$ regular, and translations carry this to every closed
point.

*Reducedness.* A regular local ring is a domain
([Stacks 00NP](https://stacks.math.columbia.edu/tag/00NP)), so every
local ring of $\mathcal G$ at a maximal ideal is reduced; a nonzero
global nilpotent would have a proper annihilator, hence survive in some
localization. Thus $\mathcal G$ is reduced, so
$\mathcal G=\mathcal G_{\mathrm{red}}$, which is smooth by (2) of
[lem-wf-same-lie-closed-subgroup].

*Subgroup schemes.* Stabilizer, centralizer and kernel loci are closed
subgroup schemes, so the reducedness just proved applies to them
verbatim: their defining equations already compute the tangent space,
and no passage to the reduced structure is involved.

Compare Milne, *Algebraic Groups* (2017), Cartier's Theorem 3.23.
Quoted rather than proved, all general geometry: density
([Stacks 0B8X](https://stacks.math.columbia.edu/tag/0B8X)) and openness
([Stacks 01V5](https://stacks.math.columbia.edu/tag/01V5)) of the smooth
locus over a perfect field, with the regularity criterion
([Stacks 00TV](https://stacks.math.columbia.edu/tag/00TV)), and the
regular-local-domain theorem.
