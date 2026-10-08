+++
id = "lem-fin-finite-type-pushforward-embedding"
kind = "lemma"
title = "Finite-pushforward embeddings over a field"
order = 1607
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lem-fin-normal-generic-constant", "lem-fin-normalization-extension-finite", "lem-weil-pbc-constructible-noetherian-finite-selection"]
+++
Let $X$ be of finite type
over a field, and let $F$ be a
constructible
sheaf of $\mathbf Z/N$-modules. There are finitely many finite maps
$h_i:Y_i\to X$, finite groups $M_i$ killed by $N$, and an
injective map

$$
F\longrightarrow\bigoplus_i(h_i)_*\underline M_i .
$$

Direct images have the meaning of [def-weil-pbc-direct-image].

## Proof

Fix $x\in X$. The restriction of $F$ to
$\operatorname{Spec}\kappa(x)$ is finite locally constant, by
[def-weil-pbc-constructible-complexes].
One member of a trivializing etale cover gives a finite separable
extension $K/\kappa(x)$ on which it becomes constant, say $M$.
Let $Z=\overline{\{x\}}_{\mathrm{red}}$, and normalize $Z$ in $K$.
This gives $h:Y\to Z\to X$, finite by
[lem-fin-normalization-extension-finite]. Its source is normal
integral and Noetherian, with generic inclusion $e:\operatorname{Spec}K\to Y$.
Write $a=he$. The adjunction of
[def-weil-pbc-inverse-image], [def-weil-pbc-direct-image] gives

$$
F\longrightarrow a_*a^*F
\simeq h_*e_*\underline M
\simeq h_*\underline M ,
$$

where the last isomorphism is
[lem-fin-normal-generic-constant].
At a geometric point above $x$, compose this map with evaluation
at the chosen generic geometric point of $Y$.
The composite is the identity of $F_{\bar x}=M$, by the
unit–counit identity. Hence the displayed map is injective at
$\bar x$. It is a map of $\mathbf Z/N$-modules throughout.

Perform this construction for every $x$.
The finite-selection lemma
[lem-weil-pbc-constructible-noetherian-finite-selection]
chooses finitely many of these maps whose direct sum is injective
on every stalk, and therefore injective as a sheaf map.
No normalization in an infinite extension, approximation, or
higher-direct-image finiteness is used.
