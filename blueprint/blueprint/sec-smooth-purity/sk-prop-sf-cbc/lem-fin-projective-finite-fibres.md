+++
id = "lem-fin-projective-finite-fibres"
kind = "lemma"
title = "Projective morphisms with finite fibres are finite"
order = 1596
uses = ["def-pc-projective-morphism", "def-pc-projective-space-twist", "def-weil-pbc-scheme-conventions", "lem-pc-projective-coherent-finiteness", "lem-pc-projective-proper", "lem-pc-projective-space-serre-vanishing", "lem-weil-pbc-proper-closed-image"]
+++
Let $f:D\to T$ be a
projective morphism with
Noetherian target.
If every geometric fibre has only finitely many points, then $f$
is finite.

## Proof

Fix $t\in T$. By [def-pc-projective-morphism], after
restriction to an affine neighbourhood
$T_0=\operatorname{Spec}A$ of $t$, choose a closed immersion
$D_{T_0}\hookrightarrow\mathbf P^N_A$.
Write $\mathfrak p$ for the prime of $A$ corresponding to $t$,
and put $\kappa=\kappa(t)$.

The fibre $D_t$ is a finite $\kappa$-scheme. Here finiteness
follows directly from the fibre hypothesis: a positive-dimensional
finite-type scheme over an algebraically closed field has infinitely
many closed points, by Noether normalization on a positive-dimensional
affine component. Thus $D_t$ is zero-dimensional. Its finitely
many points are all closed, so its topology is discrete. Each point
has an affine neighbourhood, which can be restricted to that
singleton. Its Noetherian zero-dimensional local ring is Artinian.
Its residue field is finite over $\kappa$ by Zariski's lemma, and
its finite filtration by powers of the maximal ideal has finite
dimensional residue-field quotients. Consequently this local ring
is a finite dimensional $\kappa$-algebra. Taking the finite
disjoint union proves that $D_t$ is affine and finite over $\kappa$.

Let $I_t$ be the coherent ideal of
$D_t\hookrightarrow\mathbf P^N_\kappa$.
For all sufficiently large $m>0$,
[lem-pc-projective-space-serre-vanishing] gives
$H^1(\mathbf P^N_\kappa,I_t(m))=0$. The ideal exact sequence,
with the twist of [def-pc-projective-space-twist], therefore
gives a surjection

$$
H^0(\mathbf P^N_\kappa,\mathcal O(m))
\longrightarrow H^0(D_t,\mathcal O(m)|_{D_t}).
$$

An invertible module over the Artinian ring of $D_t$ is free
of rank one on each local factor, hence free of rank one on the
product. Choose a generator of $\mathcal O(m)|_{D_t}$, and
lift it by this surjection to a homogeneous polynomial $P_t$.
If $D_t$ is empty, take any homogeneous polynomial of positive
degree instead. In both cases $P_t$ has no zero on $D_t$.

The finitely many coefficients of $P_t$ belong to
$\kappa=A_{\mathfrak p}/\mathfrak pA_{\mathfrak p}$.
Lift them to $A_{\mathfrak p}$ and clear their finitely many
denominators, all of which lie outside $\mathfrak p$.
This gives $a\notin\mathfrak p$ and a homogeneous polynomial
$P$ over $A_a$ restricting to $P_t$.
The closed subscheme

$$
E=D_{A_a}\cap V_+(P)\subseteq\mathbf P^N_{A_a}
$$

is projective, hence proper by [lem-pc-projective-proper].
Its image in $\operatorname{Spec}A_a$ is closed by
[lem-weil-pbc-proper-closed-image], and does not contain $t$.
Choose a principal affine neighbourhood $V$ of $t$ inside
the complement of that image. Then $D_V$ is contained in the
standard affine open $D_+(P)$ of projective space over $V$.
It is closed in that affine open, and is therefore affine.

The morphism $D_V\to V$ is still projective. Apply the
already proved [lem-pc-projective-coherent-finiteness] to
$\mathcal O_{D_V}$: the coordinate algebra
$\Gamma(D_V,\mathcal O_{D_V})$ is a finite module over the
coordinate ring of $V$. Thus $D_V\to V$ is finite by
[def-weil-pbc-scheme-conventions].
Every $t$ has such a neighbourhood. The affine-local
criterion for finiteness in the same definition proves that
$f$ is finite.
