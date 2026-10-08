+++
id = "lem-sc-morphism-from-function"
kind = "lemma"
title = "Rational functions define finite morphisms to $\\mathbf P^1$"
order = 699
uses = ["def-sc-curves", "def-sc-function-field", "lem-sc-dim0-finite", "lem-sc-rational-function-morphism", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular", "thm-pqf-finite-iff-proper-finite-fibres"]
+++
Let $C$ be a proper smooth connected curve over
$k$, $f\in k(C)\setminus k$ ([def-sc-function-field]),
and $\pi_f:C\to\mathbf P^1_k$ the morphism of
[lem-sc-rational-function-morphism]. Then $\pi_f$ is
finite surjective and flat of degree $[k(C):k(f)]$.

## Proof

By [lem-sc-rational-function-morphism], $\pi_f$ is defined
with $\pi_f^*t=f$.

*Surjectivity and finiteness.* The image of $\pi_f$ is not a
point (otherwise $\pi_f^*t=f\in k$), so it is closed (properness)
and of dimension one, hence all of $\mathbf P^1_k$: $\pi_f$ is
surjective. The fibres of $\pi_f$ are finite: the fibre over
$y\in\mathbf P^1$ is a proper closed subscheme of $C$ not equal
to $C$, hence of dimension zero and finite by
[lem-sc-dim0-finite]. A proper morphism with finite fibres is
finite ([thm-pqf-finite-iff-proper-finite-fibres] of the quasi-finite chapter, i.e. proper and quasi-finite implies finite:
*Stacks Project, Cohomology of Schemes, [Tag 02OG](https://stacks.math.columbia.edu/tag/02OG) = Lemma 30.21.1*), so
$\pi_f$ is finite.

*Flatness and degree.* The coherent sheaf
$\mathcal E:=(\pi_f)_*\mathcal O_C$ is a subsheaf of the constant
sheaf $k(C)$ on $\mathbf P^1$: the natural map
$\pi_{f*}\mathcal O_C\to j_*j^*\pi_{f*}\mathcal O_C=j_*(k(C))$ (for
$j$ the generic point) is injective because $\pi_f$ is dominant.
Hence $\mathcal E$ is torsion-free. A coherent torsion-free sheaf
on the smooth curve $\mathbf P^1$ is locally free: at a closed
point $y$, the stalk $\mathcal E_y$ is a finitely generated
module over the discrete valuation ring $\mathcal O_{\mathbf P^1,y}$
([lem-sc-smooth-regular],
[lem-sc-regular-dim1-dvr]) and is torsion-free, hence free
(finitely generated torsion-free modules over a discrete valuation
ring are free). A finite morphism is flat if and only if its
pushforward is locally free, so $\pi_f$ is finite flat. Its degree
is the rank of the locally free sheaf $\mathcal E$, which equals
$[k(C):k(f)]$: the generic stalk of $\mathcal E$ is the field
$k(C)$, viewed as a $k(\mathbf P^1)=k(t)$-vector space (and
$k(C)$ is a finite extension of $k(t)$ by standard field theory:
a finitely generated field of transcendence degree one over $k$ is
finite over $k(t)$ for any transcendental $t$).
