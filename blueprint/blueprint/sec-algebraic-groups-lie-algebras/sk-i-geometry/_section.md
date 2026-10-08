+++
id = "sk-i-geometry"
kind = "section"
title = "Basic affine geometry"
order = 2482
uses = ["sk-d-geometry", "sk-d-tangent"]
lean = ["iInf_ker_algHom_eq_nilradical", "exists_algHom_ker_eq_of_isMaximal", "exists_isOpen_inter_subset_of_isConstructible", "ringKrullDim_quotient_lt_of_finiteType", "IsRegularLocalRing.isDomain", "isReduced_tensorProduct_of_perfectField"]
+++
*Proposition (sketch).*

Finite-type affine schemes over $k$ are Noetherian (descending chains
of closed sets stabilize). They have finitely many irreducible
components. Closed points have residue field $k$, and a function on
a reduced affine variety vanishing at every $k$-point is zero.
Images of finite-type morphisms are constructible; a dense
constructible subset contains a nonempty open subset of its closure.
A proper closed subset of an irreducible variety has strictly smaller
dimension. Regular local rings are domains, so irreducible components
of a smooth variety do not meet.
A product of reduced affine varieties over $k$ is again a reduced affine
variety; the vanishing principle above therefore applies to it, so a
regular function on such a product vanishing at all its $k$-points is
zero. This is what lets a morphism defined on a product, such as a
commutator map, be tested on rational points in each variable
separately. These are the affine-geometric facts
used below with [sk-d-geometry], [sk-d-tangent].
thm:ag-noetherian;thm:ag-nullstellensatz;thm:ag-chevalley;lem:ag-constructible-open;thm:ag-dimension-drop;thm:ag-regular-domain

## Proof

*Noetherianity and components.* A finite-type coordinate algebra is a
quotient of $k[t_1,\ldots,t_n]$, Noetherian by the Hilbert basis theorem,
and quotients inherit the ascending chain condition. The correspondence
between closed sets and radical ideals of [sk-d-geometry] turns a
descending chain of closed sets into an ascending chain of ideals, which
stabilizes. In a Noetherian space, a closed set admitting no finite
expression as a union of irreducible closed sets may be chosen minimal; it
is then reducible, and both of its proper closed pieces do admit such
expressions, a contradiction. Discarding redundant members of an
expression for the whole space leaves exactly the maximal irreducible
closed subsets, finitely many of them.

*Points and the vanishing principle.* Over the algebraically closed
$k$ the Nullstellensatz gives $I(V(I))=\sqrt I$. Evaluation at a closed
point is therefore onto $k$, so its residue field is $k$; and a function
on a reduced variety vanishing at every $k$-point has a representative in
$\sqrt J=J$, hence is zero. Consequently a regular map whose values on
$k$-points lie in a closed subvariety $Z$ factors uniquely through $Z$.

*Constructibility.* Chevalley's theorem gives constructibility of the
image, the coordinate map of a finite-type morphism being finitely
presented. If a constructible set $S=\bigcup_i(U_i\cap F_i)$ is dense,
choose an irreducible component $C$; it lies in one $\overline{S_i}$,
since a finite closed cover of an irreducible space has a member equal to
the whole space. The complement $\Omega$ of the remaining components is a
nonempty open subset of the ambient space contained in
$C\subseteq\overline{S_i}$. As $S_i$ is open in its closure and dense
there, $S_i\cap\Omega$ is the required nonempty open set.

*Dimension drop.* For irreducible $X$ the algebra $k[X]$ is a domain:
if $ab=0$ then $X=V(a)\cup V(b)$, so one factor vanishes at every
$k$-point and is zero by the vanishing principle. If $Y\subsetneq X$ is
closed with radical ideal $I\ne0$, every prime chain of length $r$ in
$k[X]/I$ pulls back to a chain of primes containing $I$, and prepending
$(0)$ gives a chain of length $r+1$ in $k[X]$. Since $\dim k[X]$ is a
finite integer, $\dim Y\le\dim X-1$. The empty case is the convention
$\dim\varnothing=-1$.

*Products.* A nonzero $t=\sum_{i\le r}a_i\otimes b_i$ with the $b_i$
linearly independent has some $a_i\ne0$, hence some $x$ with
$a_i(x)\ne0$ by the vanishing principle; then $\sum_ia_i(x)b_i\ne0$ in
the second coordinate algebra, so $t(x,y)\ne0$ for some $y$. Thus
$A\otimes_kB$ embeds into functions on its $k$-points and is reduced, and
the vanishing principle applies to it. This is what lets a morphism
defined on a product, such as a commutator map, be tested on rational
points in each variable separately.

The Nullstellensatz and Chevalley's theorem are Mathlib
(`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`,
`PrimeSpectrum.isConstructible_comap_image`); compare Milne,
[Algebraic Groups](https://www.jmilne.org/math/Books/iAG2017.pdf)
(2017), Corollary 1.35 and Appendix Ag, for the product and
vanishing-ideal clauses, whose proof uses that $k$ is algebraically closed,
hence perfect. One clause is quoted rather than proved: that a regular
local ring is a domain (00NP), one of the four foundational
inputs the full source retains. It is used only to see that the
irreducible components of a smooth variety are disjoint, and again for the
reducedness clause of [sk-i-cartier].

Uses: [sk-d-geometry], [sk-d-tangent]
