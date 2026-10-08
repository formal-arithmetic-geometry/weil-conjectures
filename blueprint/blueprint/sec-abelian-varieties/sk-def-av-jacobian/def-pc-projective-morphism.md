+++
id = "def-pc-projective-morphism"
kind = "definition"
title = "Projective morphisms"
order = 449
uses = ["def-pc-scheme"]
+++
Let $f:X\to S$ be a morphism of schemes. $f$ is *H-projective*, or
*relatively projective*, if there is a closed immersion
$i:X\hookrightarrow\mathbf P^n_S$ over $S$ with $f=\pi\circ i$
($\pi:\mathbf P^n_S\to S$ the structure morphism); $f$ is
*projective* if it is H-projective and quasi-compact (Morphisms of
Schemes, Definition 29.44.1, Tag
[01W8](https://stacks.math.columbia.edu/tag/01W8); the Stacks
Project's *projective* is the form ``closed subscheme of a projective
bundle $\mathbf P(\mathcal E)$ over $S$'', while H-projective is the form
``closed immersion into some $\mathbf P^n_S$'', so the convention used here
is the H-projective one together with quasi-compactness). A scheme $X$
over a field $k$ is *projective over $k$* if the structure morphism
$X\to\operatorname{Spec}(k)$ is projective.
