+++
id = "lem-coef-normalized-dvr-effectivity"
kind = "lemma"
title = "Effectivity of a normalized DVR tower"
order = 2132
uses = ["def-coef-normalized-dvr-tower", "def-weil-derived-complete", "prop-weil-pbc-roos-triangle"]
+++
For a tower in [def-coef-normalized-dvr-tower], put
$M=R\varprojlim_m\operatorname{Res}_m M_m$. Then the canonical
counit comparisons give coherent isomorphisms

$$
M\otimes_R^L A_n\xrightarrow{\sim}M_n
\qquad(n\geq1).
$$

In particular $M$ is derived complete in the sense of
[def-weil-derived-complete]. No constructibility or boundedness
is required for this effectivity assertion.

## Proof

Fix $n$, and discard the finitely many indices $m<n$.
The coefficient complex

$$
C_{m,n}=A_m\otimes_R^L A_n
=[A_m\xrightarrow{\pi^n}A_m]
$$

is in degrees $[-1,0]$. Its augmentation to $A_n$ has
fiber $(\pi^{m-n}A_m)[1]\cong A_n[1]$, as an object of
$D(A_m)$. This identification uses multiplication by
$\pi^{m-n}$; its inverse on the fiber is determined by the
single nonzero cohomology module. For $m'\geq m\geq n$,
coefficient reduction sends the generator $\pi^{m'-n}$ to
$\pi^{m'-m}\pi^{m-n}$. Thus the fiber transition, expressed
in these copies of $A_n[1]$, is multiplication by
$\pi^{m'-m}$.

Tensor this coefficient triangle with $M_m$ over $A_m$.
The normalization and cocycle of
[def-coef-normalized-dvr-tower] give a tower of triangles

$$
M_n[1]\longrightarrow M_m\otimes_R^L A_n
\longrightarrow M_n\longrightarrow .
$$

The right-hand tower is constant, with identity transitions. The
left-hand transition for $m'\to m$ is multiplication by
$\pi^{m'-m}$: this follows by tensoring the just computed
coefficient map and using the same normalization cocycle. The
calculation is made in strict coefficient complexes and their
derived tensor products, so these are compatible triangles of
towers, not independently chosen cones.

Every $n$ successive left-hand transitions compose to zero.
In its Roos triangle of [prop-weil-pbc-roos-triangle], the
shift $s$ on the derived product therefore satisfies $s^n=0$.
The inverse of $1-s$ is $1+s+\cdots+s^{n-1}$, so this
fiber tower has zero derived limit. The quotient $A_n$ has
the bounded finite-free $R_X$-resolution
$[R_X\xrightarrow{\pi^n}R_X]$. Tensoring with it commutes
with derived products and fibers, hence with the derived limit
in the Roos triangle. Taking limits in the displayed triangles
now proves

$$
M\otimes_R^L A_n
\cong R\varprojlim_m(M_m\otimes_R^L A_n)
\xrightarrow{\sim}M_n.
$$

Every map is induced by the tower projections and coefficient
augmentations, so these isomorphisms have the stated cocycle.
They identify the original tower with the quotient tower of
$M$; its limit is $M$, proving completeness by
[def-weil-derived-complete].
For the coefficient tower itself, its derived limit is the
completed coefficient sheaf $R_X$ in degree zero: on a
weakly contractible quasi-compact pro-etale basis object, sections
are exact and the maps between the finite constant coefficient
sheaves are surjective on sections. The Roos computation therefore
has no higher inverse-limit term, and its ordinary limit is
$R_X$. This also verifies the completeness of the coefficient
object used below.
