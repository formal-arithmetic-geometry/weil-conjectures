+++
id = "lem-fin-symmetric-product-finite"
kind = "lemma"
title = "A finite symmetric-product cover over a Noetherian base"
order = 1597
uses = ["def-pc-projective-morphism", "def-weil-pbc-scheme-conventions", "def-weil-pbc-symmetric-product-morphism", "lem-chow-segre", "lem-fin-projective-finite-fibres", "lem-weil-pbc-symmetric-product-properties"]
+++
For a Noetherian scheme $S$ and $n\geq1$, the
symmetric-product map
$\sigma_n:(\mathbf P^1_S)^n\to\mathbf P^n_S$ is finite and surjective,
in the sense of [def-weil-pbc-scheme-conventions].

## Proof

Write $X=(\mathbf P^1_S)^n$, $T=\mathbf P^n_S$, and let
$\sigma_n:X\to T$ be the morphism of
[lem-weil-pbc-symmetric-product-properties].
The Segre closed immersion of
[lem-chow-segre] embeds
$X$ in a projective space $\mathbf P^M_S$.
The graph $X\to X\times_S T$ of $\sigma_n$ is closed:
it is the inverse image of the closed diagonal of the
separated scheme $T/S$, using
[def-weil-pbc-scheme-conventions].
Composing this graph with the base-changed Segre immersion gives
a closed immersion $X\hookrightarrow\mathbf P^M_T$ over $T$.
Consequently $\sigma_n$ is projective by
[def-pc-projective-morphism].

Over an algebraically closed geometric point of $T$, the
corresponding nonzero binary form of degree $n$ factors
into $n$ linear forms. Unique factorization says that every
ordered factorization is obtained by ordering the same list
of projective linear factors, counted with multiplicity.
The geometric fibre is therefore nonempty and has at most
$n!$ points. A finite-type scheme over an algebraically
closed field with positive dimension would have infinitely
many closed points, so there are no additional nonclosed
points in this fibre.
Since $T$ is Noetherian, [lem-fin-projective-finite-fibres]
proves that $\sigma_n$ is finite.
Its nonempty geometric fibre over every point proves
surjectivity in the sense of
[def-weil-pbc-scheme-conventions].
