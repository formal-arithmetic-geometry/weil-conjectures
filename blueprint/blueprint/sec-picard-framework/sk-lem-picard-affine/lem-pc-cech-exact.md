+++
id = "lem-pc-cech-exact"
kind = "lemma"
title = "The Amitsur complex of a faithfully flat ring map"
order = 606
uses = ["def-pc-scheme"]
+++
Let $A\to A'$ be a faithfully flat ring map and $M$ an $A$-module.
Then the augmented Amitsur (Cech) complex

$$
0\longrightarrow M\longrightarrow M\otimes_AA'
\longrightarrow M\otimes_AA'\otimes_AA'\longrightarrow\cdots
$$

is exact.

## Proof

Set $B=A'$. After tensoring the augmented complex with the faithfully
flat $A$-algebra $B$, put
$D^q=B\otimes_A M\otimes_A B^{\otimes_A(q+1)}$ for $q\geq0$ and
$D^{-1}=B\otimes_A M$. The differential inserts $1$ in each of the
$q+2$ slots among the last $q+1$ factors, with alternating signs.
For $q\geq0$ define

$$
h^q(b\otimes m\otimes b_0\otimes\cdots\otimes b_q)
=bb_0\otimes m\otimes b_1\otimes\cdots\otimes b_q.
$$

In $h^{q+1}d^q$, the term inserting $1$ before $b_0$ is the identity.
Each other insertion term cancels the term in $d^{q-1}h^q$ inserting
$1$ in the preceding slot, since their signs are opposite. Thus
$h^{q+1}d^q+d^{q-1}h^q=1$, including the augmentation degree.
The base-changed complex is therefore contractible. Tensoring with
$B$ is exact because $B$ is flat, so its cohomology is the original
cohomology tensored with $B$. Faithfulness then implies that the
original cohomology vanishes. This proves exactness for arbitrary
$M$, without assuming that $M$ is flat.
