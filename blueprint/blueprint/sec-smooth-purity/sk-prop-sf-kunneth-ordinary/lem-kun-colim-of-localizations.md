+++
id = "lem-kun-colim-of-localizations"
kind = "lemma"
title = "Colimit of localizations"
order = 1748
uses = ["def-kun-separably-closed", "lem-kun-algebra-union"]
+++
Let $B$ be an integral $K$-algebra which is a filtered union
$B=\bigcup_{i\in I}B_i$ of its finite type $K$-subalgebras, and
assume $L=\mathrm{Frac}(B)$ is a field (e.g. algebraically closed).
Let $J$ be the set of pairs $(i,g)$ with $i\in I$ and
$g\in B_i\setminus\{0\}$, ordered by $(i',g')\ge(i,g)$ if and only
if $B_i\subseteq B_{i'}$ and the image of $g$ in $(B_{i'})_{g'}$
is a unit. Then

$$
L=\varinjlim_{(i,g)\in J}(B_i)_g .
$$

## Proof

The order is filtered: given $(i,g),(j,h)$, choose $k$ with
$B_i,B_j\subseteq B_k$, then $(i,g),(j,h)\le(k,gh)$. Every
$(B_i)_g$ injects into $L$, so the colimit is a subring of
$L$. Conversely, for $a/b\in L$ with $a,b\in B\setminus\{0\}$,
choose $i$ with $a,b\in B_i$; then $a/b$ lies in the image of
$(B_i)_b$, so the colimit is all of $L$.
