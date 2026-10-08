+++
id = "prop-weil-pbc-preservation-constructible"
kind = "theorem"
title = "Preservation before constructible restriction"
order = 1355
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-bounded-constructible-complete", "def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-cartesian-square", "def-weil-pbc-finite-level-amplification", "def-weil-pbc-scheme-conventions", "def-weil-pbc-tower-preservation", "def-weil-pbc-witness-compatibility", "lem-weil-pbc-reconstruction-uniform-tower", "prop-weil-pbc-direct-image-limits", "thm-weil-pbc-amplification-proper"]
tags = ["latex:proposition"]
+++
Let $\square$ be the cartesian square [def-weil-pbc-cartesian-square] with
$X,Y,X',Y'$ noetherian of finite dimension, $f$ and $f'$ proper, and suppose
there is a positive integer $N$ annihilating $A/I$ which is invertible on
all four schemes. Assume that the geometric fibers of $f$ have dimension at
most $e\in\mathbf Z_{\geq0}$; put $c=2e$.

Then, for every $K\in\Dbc(X_{\Proet},A)$ whose reductions have a common
cohomological interval $[a,b]$, one has
$$
 \begin{aligned}
  Rf_*K&\in\Dbc(Y_{\Proet},A),&
  Lg^*_{\mathrm{comp}}Rf_*K&\in\Dbc(Y'_{\Proet},A),\\
  Lg'^*_{\mathrm{comp}}K&\in\Dbc(X'_{\Proet},A),&
  Rf'_*Lg'^*_{\mathrm{comp}}K&\in\Dbc(Y'_{\Proet},A).
 \end{aligned}
$$
The two pullbacks have reduction amplitude $[a,b]$ and the two direct images
have reduction amplitude contained in $[a,b+c]$.

*Source note:* no Stacks Project entry states this preservation: the
constructibility of the four outputs is the adic constructibility of
Definition 61.29.1 ([Tag 09C1](https://stacks.math.columbia.edu/tag/09C1))
and Proposition 61.29.7 ([Tag
09C7](https://stacks.math.columbia.edu/tag/09C7)), and the amplitude bounds
are those of Lemma 59.92.2 ([Tag
095U](https://stacks.math.columbia.edu/tag/095U)) and Theorem 63.14.5 ([Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0)), each stated for a single
complex on a Noetherian scheme; the closest packaged form is Lemma 61.29.2
([Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)), which realizes one
constructible $K$ as $\Rlim K_n$ with a common interval and etale origins
but says nothing about functors. The blueprint adds the simultaneous
statement for the completed pullbacks and direct images of
$\Dbc(X_{\Proet},A)$ whose reductions share the interval $[a,b]$.

## Proof

By [thm-weil-pbc-amplification-proper] the three conditions
$$
 \mathrm{AMP}(\square;2e),\qquad\mathrm{WIT}(\square),\qquad\mathrm{TOW}(\square)
$$
of [def-weil-pbc-finite-level-amplification],
[def-weil-pbc-witness-compatibility] and [def-weil-pbc-tower-preservation]
hold for $c=2e$, so the argument below applies. Let
$K\in\Dbc(X_{\Proet},A)$ have all reductions supported in $[a,b]$, so that
its reduction tower is uniformly bounded constructible in the sense of
[def-weil-pbc-bounded-constructible-complete] with compatible etale-origin
witnesses. By the amplification $\mathrm{AMP}(\square;c)$ and the tower
preservation $\mathrm{TOW}(\square)$, the levelwise tower functors carry
this tower to uniformly bounded constructible towers whose local models have
amplitude compatible with the containments, and by the witness compatibility
of [def-weil-pbc-witness-compatibility] the compatible etale-origin
witnesses are carried to compatible witnesses. By the reconstruction lemma
for uniform towers each of the four derived limits is then realized by its
local models, hence lies in the bounded constructible complete category, is
derived complete and has the stated reduction amplitude; and by the
direct-image-limits proposition the four limits are exactly $Rf_*K$,
$Lg^*_{\mathrm{comp}}Rf_*K$, $Lg'^*_{\mathrm{comp}}K$ and
$Rf'_*Lg'^*_{\mathrm{comp}}K$, which proves the assertions.
