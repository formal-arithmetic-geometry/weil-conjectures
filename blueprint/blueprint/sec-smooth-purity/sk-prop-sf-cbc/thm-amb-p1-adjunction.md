+++
id = "thm-amb-p1-adjunction"
kind = "theorem"
title = "The full projective-line adjunction"
order = 1573
uses = ["cor-weil-pbc-geometric-fiber-finite", "def-amb-p1-trace", "def-coefficient-twists-detailed", "def-sc-p1-standard", "def-weil-pbc-derived-categories", "lem-amb-p1-diagonal-integrals", "lem-amb-proper-coproducts-projection", "lem-weil-derived-direct-image-composition", "thm-amb-p1-decomposition"]
+++
On the whole ordinary derived categories of etale $A$-modules,

$$
Rq_*\dashv q^*(1)[2]
\qquad(q:\mathbf P^1_S\to S).
$$

The counit is $\epsilon$ of [def-amb-p1-trace].
The notation refers to the projective line, and Tate twists.

## Proof

Write $F=Rq_*$, $G=q^*(1)[2]$. Use the notation
and the map $\delta$ of
[lem-amb-p1-diagonal-integrals]. For an arbitrary
complex $M$ on $P$, define

$$
\eta_M:M=R(p_2)_*\Delta_*M
\xrightarrow{R(p_2)_*(\delta\otimes p_1^*M)}
R(p_2)_*p_1^*M(1)[2]
\xrightarrow{\sim} q^*Rq_*M(1)[2]=GFM.
$$

Here $\Delta_*M\cong\Delta_*A\otimes_A^Lp_1^*M$
by the closed-immersion projection formula (or directly on
geometric stalks), and the last arrow is proper base change
[cor-weil-pbc-geometric-fiber-finite], extended to
complexes as in [lem-amb-proper-coproducts-projection].
Thus $\eta$ is a natural transformation on all complexes.
Set $\epsilon$ equal to the natural transformation in
[def-amb-p1-trace].

We verify both triangles, keeping track of the coordinate
integrated in each. For the first triangle, the composite
$\epsilon_{FM}\circ F\eta_M$, after proper base change,
the projection formula and the composition
$R(qp_1)_*\cong Rq_*Rp_{1*}$ of
[lem-weil-derived-direct-image-composition] (item (5)), is

$$
\begin{split}
Rq_*M
&=R(qp_1)_*\Delta_*M\\
&\longrightarrow R(qp_1)_*p_1^*M(1)[2]\\
&\cong Rq_*\bigl(M\otimes_A^LR(p_1)_*A_W(1)[2]\bigr)\\
&\xrightarrow{Rq_*(1_M\otimes t_{p_1})}Rq_*M.
\end{split}
$$

By the base-change compatibility of
[thm-amb-p1-decomposition], $t_{p_1}$ is the
pullback of $t_q$ along $q:P\to S$, under
the proper base-change identification for $p_1$.
Indeed $\eta$ first sums over the first coordinate,
whereas $\epsilon_{FM}$ then integrates the second
coordinate. The equality $qp_1=qp_2$ and the
composition isomorphism for derived direct images interchange
these two operations; the exchange map is obtained from the
same pullback counits on the Cartesian square. Naturality
of the tensor projection map identifies the resulting first
arrow with $1_M\otimes R(p_1)_*\delta$.
Consequently the whole composite is $Rq_*$ of $1_M$
tensored with
$t_{p_1}\circ R(p_1)_*\delta$. This is the identity
by [lem-amb-p1-diagonal-integrals].

For the other triangle, substitute $M=GK$ in $\eta$.
Since $p_1^*q^*K=p_2^*q^*K$, the projection formula
pulls this common coefficient out of $R(p_2)_*$.
The map $G\epsilon_K$ integrates the first coordinate
of $W$, and is therefore $t_{p_2}$ on the remaining
kernel factor. Hence

$$
G\epsilon_K\circ\eta_{GK}
=1_{q^*K(1)[2]}\otimes
\bigl(t_{p_2}\circ R(p_2)_*\delta\bigr)
=1_{GK}.
$$

The rearranged shifts are all even, so these rearrangements
introduce no Koszul sign. This proves the second triangle.
In these calculations the exchange and projection maps are
the canonical ones, not unspecified isomorphisms: their
compatibility is obtained by substituting their definitions
from pullback counits before applying derived direct image.
Both expressions use the same counit once in each coordinate.
The two verified triangles prove the stated adjunction.
