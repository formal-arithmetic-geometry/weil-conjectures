+++
id = "thm-zl-relative-noether"
kind = "theorem"
title = "Relative Noether normalization"
order = 2826
uses = ["def-sbc-affine-space", "def-weil-pbc-scheme-conventions", "def-zl-localized-coordinates", "lem-zl-affine-partition", "lem-zl-spread-normalization"]
+++
Let $f:X_0\to Y_0$ be a
separated finite-type
morphism of separated finite-type $k_0$-schemes.
There are finite partitions of source and target by locally closed
reduced subschemes such that each source piece $X'_0$, mapping to
a target piece $Y'_0$, has
coordinates inducing a
factorization

$$
X'_0\xrightarrow{\nu}\mathbf A^d_{Y'_0}
\longrightarrow\mathbf A^{d-1}_{Y'_0}\longrightarrow\cdots
\longrightarrow\mathbf A^1_{Y'_0}\longrightarrow Y'_0
$$

with $\nu$ finite and all subsequent arrows the coordinate
projections of relative affine space.
For $d=0$, the factorization consists just of the finite map
$X'_0\to Y'_0=\mathbf A^0_{Y'_0}$.

## Proof

All schemes under consideration are Noetherian. We use induction
on closed subsets of the target, with their reduced structures.
This induction terminates because a Noetherian space has no infinite
strictly descending chain of closed subsets.

For a nonempty reduced target $Y$, take the finitely many
irreducible components. In each component choose a nonempty
affine open avoiding all the other components. These give disjoint
integral affine opens $V_j=\operatorname{Spec}A_j$ of $Y$;
their union contains every generic point of $Y$.
For each $j$, apply [lem-zl-affine-partition] to
$X_0\times_{Y_0}V_j$. The resulting finitely many reduced affine
pieces are $\operatorname{Spec}B_{ji}$, with $B_{ji}$
a finitely generated $A_j$-algebra.

Apply [lem-zl-spread-normalization] to every $A_j\to B_{ji}$.
For fixed $j$, multiply the finitely many nonzero denominators
to obtain $s_j$. Localizing the resulting finite module
generators once more preserves their generation, so all pieces
over $D(s_j)\subset V_j$ simultaneously have finite maps to
relative affine spaces. These maps are the explicit
[def-zl-localized-coordinates] maps.
The open subset $V=\bigcup_jD(s_j)$ still contains every generic
point of $Y$, and its pieces and their inverse images give the
required finite partitions over $V$.

The complement $Y\setminus V$ is a proper closed subset.
Apply the induction hypothesis to the restriction of $f$ over
this complement. Reduced source pieces factor through the reduced
target, since a nilpotent section maps to zero in a reduced ring.
Combining those partitions with the pieces over $V$ gives finite
partitions of source and target by locally closed reduced
subschemes, as in [def-weil-pbc-scheme-conventions].
Finally the standard coordinate projections factor each
$\mathbf A^d_{Y'_0}\to Y'_0$ into the $d$ relative affine-line
projections of [def-sbc-affine-space].
