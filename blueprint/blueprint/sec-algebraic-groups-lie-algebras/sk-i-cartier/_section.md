+++
id = "sk-i-cartier"
kind = "section"
title = "Characteristic-zero group smoothness"
order = 2489
uses = ["sk-d-geometry", "sk-d-tangent", "sk-i-geometry"]
lean = ["AlgebraicGeometry.isReduced_of_grpObj", "AlgebraicGeometry.smooth_of_grpObj_of_charZero", "Matrix.GeneralLinearGroup.lieAlgebra_identityComponent", "Matrix.GeneralLinearGroup.finrank_lieAlgebra_eq_ringKrullDim", "Matrix.GeneralLinearGroup.dualUnit_add"]
+++
*Proposition (sketch).*

Every finite-type matrix group scheme over $k$ is
smooth and reduced. Thus $\dim\Lie(G)=\dim G$ for a
matrix algebraic group. Its identity component
is open and has the same tangent algebra as the whole group.
Closed subgroup schemes defined by stabilizer and centralizer equations
are included; no passage to the reduced structure changes their tangent
spaces in this characteristic-zero setting.
Differentiating multiplication at $(1,1)$ gives $(X,Y)\mapsto X+Y$.
thm:ag-cartier;cor:ag-cartier-reduced;thm:alg-tangent-dimension;lem:ag-component-lie;lem:ag-multiplication-differential

## Proof

*Reduction and smoothness of reduced groups.* The reduction
$\mathcal G_{\mathrm{red}}$ has the same $k$-points as $\mathcal G$, since
nilpotents die in $k$, and those points form a subgroup. Its
multiplication is defined on a product of reduced varieties, reduced by
[sk-i-geometry], so multiplication and inversion factor through the
reduction by the vanishing principle there; thus
$\mathcal G_{\mathrm{red}}$ is a matrix algebraic
group. Such a group is smooth: it has a dense smooth open locus, which
contains a $k$-point $a$; translation by $ga^{-1}$ is an isomorphism
carrying $a$ to any $g\in G(k)$ and preserving regularity of the local
ring; and smoothness at all closed points suffices, the nonsmooth locus
being closed and, if nonempty, containing a $k$-point.

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

*Reducedness and the dimension formula.* A regular local ring is a
domain by the clause quoted in [sk-i-geometry], so every local ring of
$\mathcal G$ at a maximal ideal is reduced; a nonzero global nilpotent
would have a proper annihilator, hence survive in some localization.
Thus $\mathcal G$ is reduced. For a matrix algebraic group, smoothness
gives $\dim_kT_1G=\dim_1G$, translations make all local dimensions at
$k$-points equal, and the global dimension is their maximum; since
$T_1G=\Lie(G)$ by [sk-d-tangent], this is $\dim\Lie(G)=\dim G$.

*Identity component and subgroup schemes.* There are finitely many
components by [sk-i-geometry], each closed, so each is open; and
restricting to an open neighborhood of $1$ changes neither the local ring
nor its cotangent space, whence $\Lie(G^\circ)=\Lie(G)$. Stabilizer and
centralizer loci are closed subgroup schemes, so the reducedness just
proved applies to them verbatim: their defining equations already compute
the tangent space, and no passage to the reduced structure is involved.

*Multiplication.* Algebra-valued points of a product are pairs, and
$(1+\varepsilon X)(1+\varepsilon Y)=1+\varepsilon(X+Y)$ in the dual
numbers of [sk-d-tangent], which is the asserted differential.

Compare Milne, [Algebraic
Groups](https://www.jmilne.org/math/Books/iAG2017.pdf) (2017), Cartier's Theorem 3.23 and Proposition 1.37; the
subgroup-scheme clause is what lets the tangent spaces of stabilizers and
centers be read off from their equations. Three clauses are quoted rather
than proved, all of them general geometry rather than group theory: density
(0B8X) and openness (01V5) of the smooth locus over a
perfect field, with the regularity criterion (00TV), together with
the regular-local-domain theorem of [sk-i-geometry]. Cartier's theorem
itself is proved.

Uses: [sk-d-geometry], [sk-d-tangent], [sk-i-geometry]
