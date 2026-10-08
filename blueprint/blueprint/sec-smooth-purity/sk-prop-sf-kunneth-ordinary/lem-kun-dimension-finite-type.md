+++
id = "lem-kun-dimension-finite-type"
kind = "lemma"
title = "Finiteness of the dimension of a finite type scheme"
order = 1676
uses = ["def-kun-dimension", "lem-kun-dimension-formula"]
+++
Let $K$ be a field and $X$ a scheme of finite type over $K$.
Then $\kundim X<\infty$.

## Proof

Every point $x\in X$ lies in an affine open chart, so
$\mathcal O_{X,x}$ is a Noetherian local ring and has finite
dimension by Krull's principal ideal theorem, while $\kappa(x)$ is a
finitely generated field extension of $K$ and has finite
transcendence degree; by [lem-kun-dimension-formula] therefore
$\kundim_xX<\infty$ for every $x\in X$ (and $X=\emptyset$ is
trivial). The Krull dimension of $X$ is the supremum of the numbers
$\kundim_xX$, $x\in X$: for an irreducible scheme every nonempty
open subset has the dimension of the scheme, so a generic point of an
irreducible component realizes the dimension of that component. A
scheme of finite type over a field is Noetherian, so $X$ has finitely
many irreducible components, and the supremum is a maximum of finitely
many finite numbers by [def-kun-dimension].
