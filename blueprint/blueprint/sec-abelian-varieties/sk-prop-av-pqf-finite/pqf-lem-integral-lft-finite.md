+++
id = "pqf-lem-integral-lft-finite"
kind = "lemma"
title = "An integral morphism of locally finite type is finite"
order = 535
uses = ["def-weil-pbc-scheme-conventions"]
+++
An integral morphism of schemes which is locally of finite type is
finite.
(*Stacks Project, Morphisms of Schemes, Lemma 29.45.4, Tag
[01WJ](https://stacks.math.columbia.edu/tag/01WJ).*)

## Proof

We work ring-locally. If
$A\to B$ is an integral ring map and $B$ is a finite type
$A$-algebra, then $B$ is a finite $A$-module: writing
$B=A[b_1,\dots,b_m]$, the case $m=1$ is the reduction of the monic
equation of $b_1$ (every higher power reduces to a combination of
$1,b_1,\dots,b_1^{n-1}$), and for $m>1$ we iterate using that an
integral element over $A$ remains integral over a larger
$A$-algebra, and that a finite module over a finite module is finite.
Now let $f:X\to S$ be integral and locally of
finite type; $f$ is affine, so for $V=\operatorname{Spec}A$ affine
open of $S$ and $f^{-1}(V)=\operatorname{Spec}B$, the map $A\to B$ is
integral, and by local finite type of $f$, after shrinking $V$ and
$f^{-1}(V)$ if necessary, $B$ is a finite type $A$-algebra (a
morphism between affines is locally of finite type exactly when the
ring map is such, and on a finite affine cover the source rings are
finite type over the target rings by
[def-weil-pbc-scheme-conventions]); by the classical
fact above $B$ is a finite $A$-module, so $f_*\mathcal O_X$ is a
finite $\mathcal O_S$-module locally, and $f$ is finite.
