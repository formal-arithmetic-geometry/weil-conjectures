+++
id = "thm-weil-pbc-amplification-proper"
kind = "theorem"
title = "Amplification for proper base-change squares"
order = 1354
uses = ["def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-cartesian-square", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-finite-level-amplification", "def-weil-pbc-scheme-conventions", "def-weil-pbc-tower-preservation", "def-weil-pbc-witness-compatibility", "lem-weil-pbc-comparison-pullback", "lem-weil-pbc-pullback-preserves-bounded-constructible", "prop-weil-pbc-amplification-consequences", "prop-weil-pbc-comparison-direct-image", "thm-weil-pbc-direct-image-finiteness-proper"]
+++
Let $\square$ be the cartesian square [def-weil-pbc-cartesian-square] with
$X,Y,X',Y'$ noetherian of finite dimension, $f$ and $f'$ proper, and suppose
there is a positive integer $N$ annihilating $A/I$ which is invertible on
all four schemes. Assume that the geometric fibers of $f$ have dimension at
most $e\in\mathbf Z_{\geq0}$. Then
$$
 \mathrm{AMP}(\square;2e),\qquad\mathrm{WIT}(\square),\qquad\mathrm{TOW}(\square)
$$
of [def-weil-pbc-finite-level-amplification],
[def-weil-pbc-witness-compatibility] and [def-weil-pbc-tower-preservation]
all hold.

*Source note:* no Stacks Project entry states this assembly: the ingredients
are the proper finiteness theorem of SGA 4 1/2, whose Stacks amplitude form
is Lemma 59.92.2 ([Tag 095U](https://stacks.math.columbia.edu/tag/095U):
$R^qf_*=0$ for $q>2n$ and abelian torsion coefficients, all fibres of
dimension $\le n$) and whose compact-support form is Theorem 63.14.5 ([Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0): constructibility of
$Rf_!K$ for $K\in D^+_{tors,c}$), together with Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)), Proposition 61.29.7 ([Tag
09C7](https://stacks.math.columbia.edu/tag/09C7)) and the reduction-tower
bounds of Lemma 61.29.2 ([Tag
09C2](https://stacks.math.columbia.edu/tag/09C2)); the blueprint adds the
simultaneous assertion of $\mathrm{AMP}$, $\mathrm{WIT}$ and $\mathrm{TOW}$
for a proper square with fibres of dimension at most $e$.

## Proof

*step (a), AMP.* In the quotient datum of the adic coefficient datum, the
condition $N(A/I)=0$ means $N\in I$. Hence $N^nP_n=0$, and $N^n$ is
invertible on the four schemes for every $n\geq1$. The geometric fibers of
$f'$ are base changes of those of $f$, hence of dimension at most $e$, so
[thm-weil-pbc-direct-image-finiteness-proper] gives
$\mathrm{FIN}(f,P_n;2e)$ and $\mathrm{FIN}(f',P_n;2e)$ for every $n\geq1$,
i.e. clause (i) of [def-weil-pbc-finite-level-amplification]; clause (ii) is
[lem-weil-pbc-pullback-preserves-bounded-constructible] for the two
pullbacks.

*step (b), WIT.* The finite-level functors commute with the normalization
isomorphisms for $P_{n+1}\to P_n$: for the direct images this is the
projection-formula compatibility of the reduction maps (the tensor with the
perfect $P_n$ commuting with $Rf_{*,n+1}$), and for the pullbacks it is the
tensor compatibility of inverse image with the quotient maps. A compatible
etale-origin witness [def-weil-pbc-etale-origin-witness]
$K_n\cong\nu_X^*L_n$ is transported: for the direct images by
$$
 Rf_{*,n}K_n\cong Rf_{*,n}\nu_X^*L_n\cong\nu_Y^*Rf_{\Et,*}L_n
$$
of [prop-weil-pbc-comparison-direct-image] (the quotient tower being built
from the same $L_n$), and for the pullbacks by
[lem-weil-pbc-comparison-pullback]; the compatibility of the transported
witnesses is the above commutation with the normalizations. Hence
$\mathrm{WIT}(\square)$.

*step (c), TOW.* A uniformly bounded constructible tower is compatibly
witnessed on the local models $L_{\alpha j}$ supported in $[d_0,d_1]$ with
finite lisse cohomology reductions, and step (b) transports the witnesses.
The levelwise direct images are therefore etale-origin; their reduction
cohomology is bounded constructible by
[thm-weil-pbc-direct-image-finiteness-proper] with the amplitude containment
of [prop-weil-pbc-amplification-consequences], and the local models are
obtained from the etale-origin descriptions: a finite lisse module is finite
locally constant, which is exactly what the tower condition requires, while
no freeness is needed or available, a finite module over a finite local ring
being possibly non-free (for instance $\mathbf Z/2$ over $\mathbf Z/4$). The
pullback side is [lem-weil-pbc-pullback-preserves-bounded-constructible].
The output tower is hence uniformly bounded constructible, i.e.
$\mathrm{TOW}(\square)$.

The source text records that audit item BC-07 was resolved by correcting the
definition rather than the proof: the bounded constructible tower and the
tower-preservation condition formerly required the local models to have
finite locally *free* terms, which a general constructible complex does not
have. The requirement is now finite local constancy, which is exactly what
finite lissity gives.
