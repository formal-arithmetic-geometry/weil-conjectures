+++
id = "thm-fin-projective-line-constructible"
kind = "theorem"
title = "Constructible coefficients on the projective line"
order = 1618
uses = ["cor-fin-projective-curve-finite-group", "def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-fin-finite-morphism", "lem-fin-finite-over-projective", "lem-fin-finite-type-pushforward-embedding", "lem-weil-pbc-grothendieck-spectral-sequence", "sbc-def-coefficient-conventions", "thm-constructible-serre", "thm-sp-if-e1"]
+++
Let $S$ be of finite type
over $k$, and let $\Lambda$ be the finite ring killed by an
integer invertible in $k$ of [sbc-def-coefficient-conventions].
For every constructible
$\Lambda$-sheaf $F$ on $\mathbf P^1_S$, every
higher direct image
$R^q\pi_*F$, for $\pi:\mathbf P^1_S\to S$, is constructible.

## Proof

First regard $F$ as a sheaf of $\mathbf Z/N$-modules.
Apply [lem-fin-finite-type-pushforward-embedding] to embed it
into a finite sum $G^0$ of finite pushforwards of constant finite
groups killed by $N$.
The sheaf $G^0$ is constructible by [lem-fin-finite-morphism];
its cokernel $Q_1$ is constructible by
[thm-constructible-serre].
Repeat with $Q_1$, and inductively with every subsequent cokernel.
Factoring the differentials through those cokernels produces an exact
augmented complex

$$
0\to F\to G^0\to G^1\to\cdots ,
\qquad G^a=\bigoplus_i(h_{ai})_*\underline {M_{ai}},
$$

with each $h_{ai}:Y_{ai}\to\mathbf P^1_S$ finite.
By [lem-fin-finite-over-projective], $Y_{ai}\to S$ is projective.
Its geometric fibres have dimension at most one, since they are
finite over a projective line. Thus
[cor-fin-projective-curve-finite-group] applies to $M_{ai}$.
Finite exactness and the composition sequence of
[lem-fin-finite-morphism], [lem-weil-pbc-grothendieck-spectral-sequence]
give

$$
R^b\pi_*G^a
=\bigoplus_i R^b(\pi h_{ai})_*\underline {M_{ai}},
$$

which is constructible in every degree.

Now use [thm-sp-if-e1] for the ordinary bounded-below resolution:

$$
E_1^{a,b}=R^b\pi_*G^a\Longrightarrow R^{a+b}\pi_*F,
\qquad a,b\geq0.
$$

All pages are constructible by kernels and cokernels.
For any fixed total degree, first-quadrant convergence supplies
a finite filtration by stable terms of this spectral sequence.
Extensions therefore prove constructibility of the abutment by
[thm-constructible-serre].
This step establishes constructibility degree by degree.

Finally these are also the underlying abelian higher direct images
of the original $\Lambda$-sheaf. Here is an explicit simultaneous
computation. Choose a conservative family $P$ of geometric points
of $\mathbf P^1_S$, let $e^*$ take the family of stalks, and set
$e_*((M_x))=\prod_{x\in P}x_*M_x$.
Both $e_*$ and $\pi_*e_*$ are exact on families of modules:
on any etale object their sections are products of the module
coordinates, and products of surjections of modules are surjective.
Also $e_*$ preserves injectives, being right adjoint to the exact
stalk functor $e^*$.
The ordinary composition spectral sequence therefore makes every
$e_*((M_x))$ acyclic for $\pi_*$.
Iterate the injective unit $E\to e_*e^*E$ on its successive
cokernels. This is an acyclic resolution, with all maps
$\Lambda$-linear; it remains an acyclic resolution on underlying
abelian sheaves by the identical argument.
Thus it computes both higher direct images, with the same
underlying abelian cohomology.
This argument uses products of modules in an explicit section
calculation, and does not assert that arbitrary products of
epimorphisms of sheaves are epimorphisms.
On each finite locally constant abelian stratum the finitely many
scalar actions are maps of finite locally constant sheaves.
A common etale refinement makes their values constant. The given
module identities then identify the stratum with a constant finite
$\Lambda$-module, proving the module constructibility required
by [def-weil-pbc-constructible-complexes].
