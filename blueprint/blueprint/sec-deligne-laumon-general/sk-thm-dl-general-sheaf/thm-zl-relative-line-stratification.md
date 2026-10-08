+++
id = "thm-zl-relative-line-stratification"
kind = "theorem"
title = "Stratification of a sheaf on a relative line"
order = 2847
uses = ["def-sbc-affine-space", "def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "i-topology", "lem-zl-affine-partition", "pqf-def-quasifinite"]
+++
Let $Y_0$ be a separated finite-type $k_0$-scheme and let $\mathcal F$
be a constructible Weil sheaf on $\mathbf A^1_{Y_0}$ (in the
constructible conventions of [def-weil-pbc-constructible-complexes]).
There are finite stratifications of source and target such that
$\mathcal F$ is lisse on every source stratum and each induced map is
either separated quasi-finite or smooth with one-dimensional affine
geometric fibers.

## Proof

We work with reduced strata; by [i-topology], nilpotent thickenings do not change the
etale coefficient categories. We induct on closed subsets of the
Noetherian target, and first explain the step on an integral affine
target $Y=\operatorname{Spec}B$. The scheme
$\mathbf A^1_Y$ is integral. Constructibility in
[def-weil-pbc-constructible-complexes] gives a nonempty open
$U\subset\mathbf A^1_Y$ on which $\mathcal F$ is lisse.
Let $Z=\mathbf A^1_Y\setminus U$, with its reduced closed structure.
If $Z$ is empty there is nothing to remove. Otherwise its ideal
$I\subset B[T]$ contains a nonzero polynomial $g$.
This is also nonzero over $\operatorname{Frac}B$, since $B$ is a
domain. Let $b\in B\setminus\{0\}$ be its leading coefficient.
Over $V=D(b)$, the polynomial $b^{-1}g$ is monic. Consequently

$$
B_b[T]/I B_b[T]
$$

is a finite $B_b$-module: it is a quotient of the module generated
by $1,T,\ldots,T^{\deg(g)-1}$ using that monic relation.
When $g$ has degree zero the quotient is zero. Thus $Z_V\to V$
is finite, including the empty case.

The open complement $U_V=\mathbf A^1_V\setminus Z_V$ still has
$\mathcal F$ lisse. It is an open subscheme of the smooth projection
of [def-sbc-affine-space], so $U_V\to V$ is smooth of relative
dimension one. Its geometric fibers are affine lines with finitely many
points removed. Such a fiber is affine: over the geometric residue
field it is a principal open defined by the product of the finitely
many linear factors of the removed points. It is nonempty and connected.
Choose a finite lissity stratification of $\mathcal F|_{Z_V}$.
Every resulting locally closed source stratum has finite geometric
fibers over $V$, and hence is separated quasi-finite by
[pqf-def-quasifinite]. We have obtained exactly the two asserted
types over the nonempty target open $V$.

For an arbitrary nonempty reduced target, choose in each of its finitely
many irreducible components an affine open avoiding all other components.
These disjoint integral opens contain all generic points. The affine
refinement can also be made using [lem-zl-affine-partition].
Perform the preceding construction on each, and take the union of the
resulting nonempty opens $V$. Its complement is a proper closed
subset of the target. Apply the induction hypothesis to the relative
affine line and the restricted sheaf over that complement. This gives
finitely many further strata. Noetherian induction terminates, so the
combined source and target partitions are finite. Refining the lissity
partitions of the quasi-finite pieces to open–closed filtrations does
not change their quasi-finiteness, and makes all gluing steps compatible
with localization.

All lissity loci can be chosen over the finite-field model: lissity is
preserved by the Weil isomorphism. Equivalently, descend the finitely
many constructible strata to a common finite constant extension and
intersect their finitely many Frobenius conjugate dense opens; this
retains the lisse open used above. The closed complements and their
successive strata are then Weil-stable. Thus the filtration is a
filtration by Weil sheaves, not just by unrelated geometric sheaves.
At no point is smoothness deduced merely from the set of points of a
fiber; it comes from restricting the known smooth affine-line projection.
