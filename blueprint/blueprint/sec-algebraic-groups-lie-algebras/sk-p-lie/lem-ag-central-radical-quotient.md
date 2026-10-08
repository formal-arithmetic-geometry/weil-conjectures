+++
id = "lem-ag-central-radical-quotient"
kind = "lemma"
title = "Central radical gives centre plus derived algebra"
order = 2472
uses = ["def-wf-lie-radical-centre", "def-wf-semisimple-lie-algebra", "lem-ag-killing-nondegenerate"]
+++
Let $L$ be a finite-dimensional Lie algebra over
$\overline{\mathbf Q}_\ell$ whose radical is central,
$\operatorname{rad}L=Z(L)$, in the notation of
[def-wf-lie-radical-centre]. Then $L/Z(L)$ is semisimple and

$$
L=Z(L)+[L,L],
$$

where the plus sign denotes a sum of subspaces.

## Proof

The quotient $\bar L=L/Z(L)$ has zero radical. Let
$\bar I\subseteq\bar L$ be a solvable ideal and let $J\subseteq L$ be its
inverse image. Then $D^nJ\subseteq Z(L)$ for some $n$, and $Z(L)$ is
abelian, so $D^{n+1}J=0$. Thus $J$ is a solvable ideal, hence is contained
in the sum of all solvable ideals, $\operatorname{rad}L=Z(L)$, and
$\bar I=0$. So $\bar L$ is semisimple in the sense of
[def-wf-semisimple-lie-algebra].

By [lem-ag-killing-nondegenerate] the Killing form $B$ of $\bar L$ is
nondegenerate. Invariance of that form gives

$$
[\bar L,\bar L]^\perp
=\{x:B([x,y],z)=0\text{ for all }y,z\}
=Z(\bar L),
$$

so the orthogonal complement of the derived algebra lies in the centre.
The centre is an abelian, hence solvable, ideal of the semisimple
$\bar L$, so it is zero; nondegeneracy then gives
$[\bar L,\bar L]=\bar L$, i.e. the quotient is perfect.

Lift an expression of each quotient class as a sum of brackets; the
difference from these lifted brackets lies in $Z(L)$. This proves
$L=Z(L)+[L,L]$, including the zero-dimensional case.
