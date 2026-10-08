+++
id = "lem-galois-object-exists"
kind = "lemma"
title = "Galois objects dominate connected objects"
order = 971
uses = ["def-galois-category", "lem-galois-axioms"]
+++
Let $(\mathcal C,F)$ be a Galois category and $X$ a connected object.
Then there is a Galois object $Z$ and a morphism $Z\to X$. (The
construction: the symmetric group acts on the $n$-fold fibre power
$X^n$, and one takes a connected component whose fibre consists of tuples
of pairwise distinct elements.)

## Proof

Let $(\mathcal C,F)$ be a Galois category as in
[def-galois-category] and let $X$ be connected. Write
$n=\#F(X)$ and consider $X^n$ with the action of $S_n$ by
permutation of the factors. By axiom (2) write
$X^n=\coprod_{t\in T}Z_t$ with $Z_t$ connected. Fix an enumeration
$s_1,\dots,s_n$ of $F(X)$; then $(s_1,\dots,s_n)\in F(X)^n=F(X^n)$
lies in $F(Z_t)$ for some $t$.
Claim 1: every element $(s_1',\dots,s_n')\in F(Z_t)$ consists of pairwise
distinct elements. Otherwise $s_i'=s_j'$ for some $i\neq j$, and then
$Z_t$ is the image of a connected component of $X^{n-1}$ under the
diagonal $\Delta_{ij}$; as a morphism from a connected object,
$\Delta_{ij}$ is an epimorphism by [lem-galois-axioms](4) and hence
induces a surjection on fibres, giving $s_i=s_j$, a contradiction.
Claim 2: the stabilizer $G=\{g\in S_n:g(Z_t)=Z_t\}$ acts transitively on
$F(Z_t)$. Indeed, for $(s_i')\in F(Z_t)$ the $s_i'$ are pairwise
distinct by Claim 1, so there is $g\in S_n$ with
$g(s_1,\dots,s_n)=(s_1',\dots,s_n')$, and then
$g(s_1,\dots,s_n)\in F(Z_t)$ forces $g(Z_t)=Z_t$.
Step 3: conclusion. Each $g\in G$ induces an automorphism of $Z_t$, and
$G\to\operatorname{Aut}(Z_t)$ is injective by
[lem-galois-axioms](6) applied to $Z_t$ and $(s_1,\dots,s_n)$.
Hence $\operatorname{Aut}(Z_t)$ acts transitively on $F(Z_t)$ by
Claim 2, so $\#\operatorname{Aut}(Z_t)\ge\#F(Z_t)$, while
$\#\operatorname{Aut}(Z_t)\le\#F(Z_t)$ by [lem-galois-axioms](6);
equality holds and $Z_t$ is Galois. The projection $X^n\to X$ to the
first factor restricts to $Z_t\to X$.
