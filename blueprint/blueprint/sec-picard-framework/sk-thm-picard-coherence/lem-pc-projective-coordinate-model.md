+++
id = "lem-pc-projective-coordinate-model"
kind = "lemma"
title = "A coordinate ring for an integral projective scheme"
order = 646
uses = ["def-pc-morphism-conventions", "def-pc-proj", "def-pc-scheme", "def-pc-standard-graded-algebra"]
+++
Let $X$ be an integral scheme over a field $k$, equipped with a
closed immersion
$i:X\hookrightarrow\mathbf P^n_k$. There is a homogeneous prime
ideal $I\subset k[x_0,\ldots,x_n]$ such that
$S=k[x_0,\ldots,x_n]/I$ is an integral
standard graded algebra
and $i$ identifies $X$ with $\operatorname{Proj}(S)$.

## Proof

Let $\eta$ be the generic point of $X$. Its image in projective space
corresponds to a homogeneous prime $I$ not containing the irrelevant
ideal, by [def-pc-proj]. This constructs $I$ without a choice of
equations or any coherent-cohomology theorem. The quotient $S$ is a
domain, its degree-zero part is $k$, and the images of the finitely
many $x_i$ generate it in degree one; these are exactly the conditions
of [def-pc-standard-graded-algebra].

We check the claimed identification on each standard affine chart of
$\mathbf P^n_k$. A nonempty inverse image in $X$ is an affine closed
subscheme of that chart and is integral. Its defining ideal is
therefore the prime ideal corresponding to its generic point, which
is $\eta$. The same prime is obtained from $I$ by homogeneous
localization followed by degree zero. Thus the chart is
$\operatorname{Spec}(S_{(x_i)})$. If the inverse image is empty,
$x_i\in I$ and the localized quotient is the zero ring, giving the
same empty chart. These identifications commute with further
localization on overlaps, so they glue to $X=\operatorname{Proj}(S)$.
