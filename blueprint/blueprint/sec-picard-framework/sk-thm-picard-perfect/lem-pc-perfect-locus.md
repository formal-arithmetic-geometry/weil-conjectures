+++
id = "lem-pc-perfect-locus"
kind = "lemma"
title = "The perfect locus with fixed degree"
order = 681
uses = ["def-pc-base-change", "def-pc-derived-category", "def-pc-derived-pullback", "def-pc-invertible-in-degree-zero", "def-pc-morphism-conventions", "def-pc-perfect-complex"]
lean = ["AlgebraicGeometry.Scheme.Modules.isOpen_setOf_hFiber_le", "AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_restrict", "AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_restrict"]
+++
Let $X$ be a scheme and let $E\in D(\mathcal{O}_X)$ be
perfect. Given $i,r\in\mathbb{Z}$ there is
an open subscheme $U\subseteq X$ characterized by the property: a
morphism $f:Y\to X$ factors through $U$ if and only if $Lf^*E$ is
isomorphic to a locally free $\mathcal{O}_Y$-module of rank $r$ placed in
degree $i$.

## Proof

If $r<0$, take $U=\varnothing$. Otherwise let $x\in X$. By
[def-pc-perfect-complex], near $x$ the object $E$ is represented
by a bounded complex $M^\bullet$ of finite free modules: the finitely
many projective terms can all be made free after shrinking.
Over the local ring $\mathcal O_{X,x}$, if a matrix of a differential
has a unit entry, row and column operations put that entry in a
$1\times1$ identity block. The equations $d^{j+1}d^j=0$ and
$d^jd^{j-1}=0$ force the adjacent maps into and out of this block
to be zero. Hence a contractible two-term summand splits off.
Each operation decreases the sum of the ranks of the terms by two,
so after finitely many operations the remaining complex has every
differential matrix in the maximal ideal.

Its residue-field differential is zero. Therefore, if
$H^j(E\otimes^{\mathbf L}\kappa(x))$ vanishes for $j\ne i$ and
has dimension $r$ in degree $i$, the remaining free terms have
rank zero except in degree $i$, where the rank is $r$.
All the changes of bases and the inverses of unit entries used in
this finite calculation are defined on an open neighbourhood of
$x$. On that neighbourhood $E$ is consequently quasi-isomorphic
to $\mathcal O^{\oplus r}[-i]$.

Define $U$ to be the set of points satisfying this residue-field
cohomology condition. The preceding construction proves that $U$
is open and that $E|_U$ is locally a free rank-$r$ module in degree
$i$. Such local descriptions agree on overlaps through the
cohomology sheaf $H^i(E)|_U$, which is therefore locally free of
rank $r$, with $E|_U\simeq H^i(E)|_U[-i]$.

If $f:Y\to X$ factors through $U$, these finite free descriptions
pull back to show that $Lf^*E$ has the required form. Conversely,
if $Lf^*E$ has that form, for any $y\in Y$ with image $x$ its
derived fibre equals
$(E\otimes^{\mathbf L}\kappa(x))\otimes_{\kappa(x)}\kappa(y)$.
Extension of fields is faithfully flat and preserves dimensions,
so $x$ satisfies exactly the defining condition of $U$. Thus the
image of $f$ is contained in $U$, which is equivalent to factoring
through that open subscheme.
