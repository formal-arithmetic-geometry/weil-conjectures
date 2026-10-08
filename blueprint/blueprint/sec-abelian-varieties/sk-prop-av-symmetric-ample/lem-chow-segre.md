+++
id = "lem-chow-segre"
kind = "lemma"
title = "The Segre embedding is a closed immersion"
order = 477
lean = ["AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi", "AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_segre", "AlgebraicGeometry.ProjectiveSpace.isProper_pi_hom"]
uses = ["def-chow-segre", "def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-projective-space-base-change", "def-weil-pbc-scheme-conventions", "lemma-nagata-projective-space-base-change-proper", "prop-nagata-proj-standard-open"]
+++
The morphism $s$ of [def-chow-segre] is a closed immersion. Consequently,
for index sets $n_1,\dots,n_m$ there are an index set $N$ and a closed
immersion of $S$-schemes

$$
\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S
\longrightarrow\mathbf P^{N}_S ;
$$

one may take $N=n_1\times\dots\times n_m$. Moreover, if all the $n_i$ are
finite, then $\mathbf P^{n_1}_S\times_S\dots\times_S\mathbf P^{n_m}_S\to S$ is
proper.

## Proof

Being a closed immersion is local on the target and on $S$, so we may assume
$S=\Spec A$ is affine and check the assertion on the standard affine charts
$D_+(X_e)\subseteq\mathbf P^N_S$, which cover $\mathbf P^N_S$. For a
multi-index $e$ one has

$$
s^{-1}\bigl(D_+(X_e)\bigr)=\prod_{i=1}^m D_+(x_{i,e_i}),
$$

which is affine, being a finite fibre product of affine schemes over the affine
base. On these charts $s$ is induced by the $A$-algebra homomorphism

$$
\mathcal O_{\mathbf P^N_S}\bigl(D_+(X_e)\bigr)
\longrightarrow
\mathcal O_{\mathbf P^{n_1}_S}\bigl(D_+(x_{1,e_1})\bigr)\otimes_A\dots
\otimes_A\mathcal O_{\mathbf P^{n_m}_S}\bigl(D_+(x_{m,e_m})\bigr),
\qquad
\frac{X_f}{X_e}\longmapsto\prod_{i=1}^m\frac{x_{i,f_i}}{x_{i,e_i}}.
$$

This homomorphism is surjective: for each $i$ and each $0\leq f_i\leq n_i$ the
multi-index $f=(e_1,\dots,e_{i-1},f_i,e_{i+1},\dots,e_m)$ satisfies
$X_f/X_e\mapsto x_{i,f_i}/x_{i,e_i}$, and these ratios generate the target as
an $A$-algebra. Hence $s$ is, locally on the target, the morphism of affine
schemes attached to a surjective ring homomorphism, i.e. a closed immersion.
Compare 01WD. (The argument above is written for a general
$m$; the formalisation carries it out for the binary case $m=2$ over
$\Spec\mathbf Z$, obtains a general base $S$ by base change, and reduces the
general $m$ to the binary case by the induction below.)

The $m$-fold statement follows by induction on the index set of the product.
For the empty product the fibre product is $S$ itself, which is
$\mathbf P^{N}_S$ for a one-element index set $N$; and if
$\mathbf P^{n_2}_S\times_S\dots\times_S\mathbf P^{n_m}_S\to\mathbf P^{N}_S$ is
a closed immersion, then so is

$$
\mathbf P^{n_1}_S\times_S\bigl(\mathbf P^{n_2}_S\times_S\dots\times_S
\mathbf P^{n_m}_S\bigr)
\longrightarrow\mathbf P^{n_1}_S\times_S\mathbf P^{N}_S
\longrightarrow\mathbf P^{n_1\times N}_S,
$$

the first morphism because closed immersions are stable under base change and
the second by the binary case.

The last assertion does not use the Segre embedding: a finite fibre product of
proper $S$-schemes is proper over $S$, because properness is stable under base
change and under composition, and $\mathbf P^{n_i}_S\to S$ is proper by
01WC.

## Detailed form

The Segre embedding of [def-chow-segre] is a closed
immersion.

## Proof

We check the criterion for a closed immersion on the distinguished affine
charts of the target, which cover $\mathbf P^N_Y$. Let $e=(e_1,\dots,e_m)$,
$0\leq e_i\leq n_i$, and let $D_+(X_e)\subseteq\mathbf P^N_Y$ be the
corresponding distinguished chart. Its preimage under $s$ is

$$
 s^{-1}(D_+(X_e))=\prod_{i=1}^m D_+(x_{i,e_i}),
$$

an affine $Y$-scheme: the chart $D_+(x_{i,e_i})$ of $\mathbf P^{n_i}_Y$ is
affine, and a finite product of affine schemes over an affine base is affine.
On these charts, after normalizing $X_e=1$ and $x_{i,e_i}=1$, the morphism $s$
is given by the ring homomorphism of polynomial rings

$$
 \mathcal O_{\mathbf P^N_Y}(D_+(X_e))
 \longrightarrow\bigotimes_{i=1}^m\mathcal O_{\mathbf P^{n_i}_Y}
 \bigl(D_+(x_{i,e_i})\bigr),
 \qquad
 \frac{X_f}{X_e}\longmapsto\prod_{i=1}^m\frac{x_{i,f_i}}{x_{i,e_i}},
$$

which sends the coordinate $\frac{X_f}{X_e}$ to the corresponding monomial.
This map is surjective: for each $i$ and each $0\leq f_i\leq n_i$, the
monomial for the multi-index $f=(e_1,\dots,e_{i-1},f_i,e_{i+1},\dots,e_m)$
equals the single ratio $x_{i,f_i}/x_{i,e_i}$, so the image contains every
generator of the target polynomial ring. Hence $s$ is affine-locally (on the
target) the morphism of affine schemes induced by a surjective ring
homomorphism, i.e. a closed immersion. Since being a closed immersion is local
on the target, $s$ is a closed immersion (cf. Stacks Project, Constructions,
Tag [01WD](https://stacks.math.columbia.edu/tag/01WD) = Lemma 27.13.6).

## Detailed form

The Segre embedding

$$
\mathbf P^m_S\times_S\mathbf P^n_S\hookrightarrow\mathbf P^{(m+1)(n+1)-1}_S
$$

is a closed immersion (over every base scheme $S$). Consequently
the tensor product $\mathcal O(1)\boxtimes\mathcal O(1)$ of very
ample modules is very ample, and the composite of a closed immersion
into $\mathbf P^N_S\times_S\mathbf P^M_S$ with the Segre embedding is
a closed immersion into a single projective space.
(*Stacks Project, Constructions of Schemes, Lemma 27.13.6,
[Tag 01WD](https://stacks.math.columbia.edu/tag/01WD).*)

## Proof

This is the recorded classical input of the statement, Stacks Project,
Constructions of Schemes, Lemma 27.13.6, [Tag
01WD](https://stacks.math.columbia.edu/tag/01WD). The two recorded consequences are immediate from it: very
ampleness is tested after a closed immersion into a projective space, and
the displayed composite of closed immersions is a closed immersion. No
separate proof is given.
