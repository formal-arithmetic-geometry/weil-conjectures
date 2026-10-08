+++
id = "lem-weil-pbc-zero-dimensional-cohomology"
kind = "lemma"
title = "Etale cohomology in dimension zero"
order = 1002
uses = ["def-weil-pbc-curve-setting", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-site", "def-weil-pbc-geometric-stalks", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $k$ be algebraically closed and let $C$ be a separated finite-type
$k$-scheme of dimension at most zero, as allowed in
[def-weil-pbc-eight-curve-assertions]. For an abelian etale sheaf
$F$, its etale cohomology is canonically

$$
 H^q(C,F)=
 \begin{cases}
  \displaystyle\prod_{c\in|C|}F_{\bar c},&q=0,\\
  0,&q>0,
 \end{cases}
$$

where the product is finite and $F_{\bar c}$ denotes the geometric stalk at
$c$.

## Proof

Finite type in the setup of [def-weil-pbc-curve-setting] gives a finite affine
cover by spectra of finite-type zero-dimensional $k$-algebras. Such rings are
Artinian; their prime ideals are finite in number and maximal, and their
residue fields are finite over $k$, hence equal to $k$. Consequently $|C|$ is
finite discrete and $C_{\mathrm{red}}=\coprod_{c\in|C|}\operatorname{Spec}k$.
The reduction is a universal homeomorphism, so invariance of the etale site
under universal homeomorphisms identifies the cohomology with that of this
finite disjoint union.

Every etale scheme over an algebraically closed field is a disjoint union of
copies of its spectrum: an affine etale neighbourhood is zero-dimensional and
reduced, and its residue fields are finite separable extensions of $k$. Thus
the small etale site on $\operatorname{Spec}k$ has sheaf category equal to the
category of sets, and abelian sheaves equal to abelian groups. Global sections
on each point are its stalk, and are exact. Global sections on the finite
disjoint union are the finite product of these exact functors. Taking their
right derived functors gives the formula.
