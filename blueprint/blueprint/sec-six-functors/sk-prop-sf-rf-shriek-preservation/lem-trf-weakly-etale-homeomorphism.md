+++
id = "lem-trf-weakly-etale-homeomorphism"
kind = "lemma"
title = "A weakly etale universal homeomorphism is an isomorphism"
order = 2074
uses = ["def-weil-scheme-morphism-properties"]
+++
Let $f:V\to W$ be a
weakly etale morphism
and a universal homeomorphism.
Then $f$ is an isomorphism.
(Source: [Stacks, Tag 0F6V](https://stacks.math.columbia.edu/tag/0F6V).)

## Proof

By [def-weil-scheme-morphism-properties], $f$ is integral,
surjective and universally injective, and both $f$ and its diagonal
are flat. The diagonal is a closed immersion, since an integral map is
separated; it is surjective on underlying points by universal
injectivity. A flat surjective closed immersion is an isomorphism.
Indeed, on affines its ring map is $R\to R/I$, where $I$ is a nil
ideal and $R/I$ is flat. Tensoring the injection $(x)\to R$ with
$R/I$, for $x\in I$, gives $(x)/I(x)=0$; hence $x=ax$ for some
$a\in I$. Since $a$ is nilpotent, $1-a$ is a unit and $x=0$.
Thus $I=0$.

The diagonal of $f$ is therefore an isomorphism, so $f$ is a
monomorphism. On an affine open of $W$, integrality makes its
inverse image affine. The resulting ring map $R\to B$ is faithfully
flat and multiplication $B\otimes_R B\to B$ is an isomorphism.
The faithfully flat equalizer
$R\to B\rightrightarrows B\otimes_R B$ identifies $R$ with all of
$B$, because the two arrows both become the identity under
multiplication. Hence $R\to B$ is an isomorphism. These affine
identifications prove the assertion.

*Recorded in advance* from chapter *The trace formula* of the source.
