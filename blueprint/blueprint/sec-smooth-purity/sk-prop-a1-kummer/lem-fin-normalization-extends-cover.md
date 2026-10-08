+++
id = "lem-fin-normalization-extends-cover"
kind = "lemma"
title = "Extending a finite cover by normalization"
order = 1907
uses = ["def-fin-normalization-extension", "def-sbc-normal-dominant-galois", "def-weil-pbc-scheme-conventions", "lem-fin-etale-normal-components", "lem-fin-normalization-extension-finite"]
+++
Let $X$ be integral of finite type over a field, let
$V\subset X$ be a nonempty normal open, and let
$P\to V$ be connected and
finite etale.
The normalization of $X$ in $k(P)$, as in
[def-fin-normalization-extension], restricts over
$V$ to the given cover $P\to V$.

## Proof

By [lem-fin-etale-normal-components], connectedness
makes $P$ normal integral. Its function field is
finite over that of $V$, because the map is finite.
On an affine open $\operatorname{Spec}B\subset V$, write
its inverse image as $\operatorname{Spec}D$. Here $D$
is a normal domain, finite and integral over $B$, with
fraction field $k(P)$. An element of $k(P)$ integral
over $B$ is also integral over $D$, hence belongs to
$D$; conversely every element of $D$ is integral over
$B$. Thus $D$ is exactly the integral closure of
$B$. This identifies the restrictions of the construction
in [def-fin-normalization-extension]; it glues because
the identifications are the identity inside the function
field. The total extension is finite by
[lem-fin-normalization-extension-finite] and has normal
integral source in the sense of
[def-sbc-normal-dominant-galois].
