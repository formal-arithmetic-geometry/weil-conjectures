+++
id = "lem-fin-finite-over-projective"
kind = "lemma"
title = "Finite covers of projective schemes are projective"
order = 1601
uses = ["def-pc-projective-morphism", "def-weil-pbc-scheme-conventions", "lem-pc-projective-proper", "lem-pc-section-clearing-denominators", "lem-weil-pbc-finite-proper", "lem-weil-pbc-proper-composition", "lem-weil-pbc-proper-immersion-closed", "lem-weil-pbc-proper-to-separated"]
+++
Let $S$ be Noetherian, $T\to S$
projective, and $h:Y\to T$
finite.
Then $Y\to S$ is projective.

## Proof

Work over an affine open of $S$, and fix $T\hookrightarrow\mathbf P^n_S$.
Let $x_i$ be the coordinate sections, $T_i=T\cap D_+(x_i)$, and
$\mathcal B=h_*\mathcal O_Y$. On each $T_i$, choose finitely many
algebra generators $b_{ij}$ of the finite algebra $\mathcal B(T_i)$.
The clearing-denominators argument of
[lem-pc-section-clearing-denominators], applied to the coherent
module $\mathcal B$ on $T$, extends $x_i^m b_{ij}$ to sections
of $\mathcal B(m)$ for one common $m\geq1$.
Increase $m$ when necessary by multiplication by $x_i$.
Include also the sections $x_i^m\cdot1$ and
$x_i^{m-1}x_j\cdot1$ for all $i,j$.
They correspond on $Y$ to sections of $h^*\mathcal O_T(m)$.
The sections $x_i^m\cdot1$ have no common zero, so the entire
finite list defines a morphism $v:Y\to\mathbf P^N_S$.

Over the target chart indexed by $x_i^m\cdot1$, the inverse image
is $h^{-1}(T_i)$. It is affine over $S$. The ratios of the chosen
sections include all $b_{ij}$ and the coordinate functions
$x_j/x_i$ of $T_i$. They therefore generate its coordinate
algebra, so $v$ is a closed immersion on that chart.
Consequently $v$ is an immersion into the union of these charts.
The source is proper over $S$ by
[lem-pc-projective-proper], [lem-weil-pbc-finite-proper], [lem-weil-pbc-proper-composition].
Thus $v$ is proper by [lem-weil-pbc-proper-to-separated],
and the immersion is closed by
[lem-weil-pbc-proper-immersion-closed].
This gives the required projective embedding locally on $S$.
