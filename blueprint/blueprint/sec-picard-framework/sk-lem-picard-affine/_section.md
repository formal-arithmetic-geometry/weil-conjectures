+++
id = "sk-lem-picard-affine"
kind = "section"
title = "Vanishing of cohomology on affine schemes"
order = 605
uses = ["sk-def-av-jacobian"]
lean = ["AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine"]
+++
*Lemma (sketch).*

Let $X=\Spec A$ be affine. For every quasi-coherent
$\cO_X$-module $\cF$ and every $q>0$: $H^q(X,\cF)=0$.

## Proof

*Step 1 (a standard covering is Čech-acyclic).* Let
$f_1,\dots,f_n\in A$ generate the unit ideal and let $M$ be an
$A$-module. The augmented alternating Čech complex

$$
0\to M\longrightarrow\prod_iM_{f_i}
\longrightarrow\prod_{i<j}M_{f_if_j}\longrightarrow\cdots
$$

is exact. Localize at one $f_j$: the covering then contains the whole
space, and inserting the index $j$ in the first slot,
$(hc)_{i_0\dots i_{q-1}}=c_{j\,i_0\dots i_{q-1}}$, is a contraction —
expanding the alternating differential gives $dh+hd=1$, the term
deleting the added $j$ being the identity and the remaining terms
cancelling in pairs. So the complex is exact after localizing at every
$f_j$. Localization is exact, so a cohomology module $N$ of the
unlocalized complex has $N_{f_j}=0$ for all $j$, i.e. every $v\in N$
satisfies $f_j^{a_j}v=0$ for some exponents; the $f_j^{a_j}$ still
generate the unit ideal, no prime containing them all, so $v=0$.

*Step 2 (the Čech vanishing criterion).* Let $\mathcal B$ be
the basis of affine opens of $X$ and $\mathrm{Cov}$ the set of standard
coverings $\{D(f_i)\}$ of members of $\mathcal B$. Then $\mathcal B$ is
closed under finite intersections (an intersection of standard opens is
standard), $\mathrm{Cov}$ is cofinal among the coverings of a
$V\in\mathcal B$ by members of $\mathcal B$ (an open of an affine is a
union of standard opens and an affine is quasi-compact, so a finite
standard subcovering exists), and by Step 1 with $M=\cF(V)$ the
augmented Čech complex of each such covering is exact in positive
degrees. The criterion then gives $H^q(X,\cF)=0$ for $q>0$.

The detailed forms are Blueprint 50, `lem-pc-affine-vanishing`
and `lem-pc-affine-cech-complex` (Step 1); the criterion of
Step 2 is Stacks, Cohomology, Lemma 20.11.9, in Section
[`01EO`](https://stacks.math.columbia.edu/tag/01EO).
