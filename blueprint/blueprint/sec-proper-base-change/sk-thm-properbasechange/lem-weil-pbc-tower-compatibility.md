+++
id = "lem-weil-pbc-tower-compatibility"
kind = "lemma"
title = "Compatibility with the coefficient tower"
order = 1345
uses = ["def-weil-pbc-four-arrows", "def-weil-pbc-four-corners", "lem-weil-pbc-finite-level-rectangle"]
+++
The transition morphisms $P_{n+1}\to P_n$ make each of the four corner
families an object
$$
 A_\bullet,B_\bullet,C_\bullet,D_\bullet
 \in D(\operatorname{Tow}_{A}(Y'))
$$
after restriction of scalars, and make $h,h',v,v'$ morphisms in this derived
tower category. Evaluation at $n$ recovers the four displayed corners and
arrows. The rectangle equation commutes with every transition and with every
compatible endomorphism of $K$.

*Source note:* no Stacks Project entry states this tower-level datum. Stacks
describes the completed pullback and its reductions for a single object
(Lemma 61.20.2, [Tag 099N](https://stacks.math.columbia.edu/tag/099N)), the
proper base-change isomorphism (Theorem 61.30.1, [Tag
09C9](https://stacks.math.columbia.edu/tag/09C9)) and, for a constructible
$K$, the structure of its reduction tower: Lemma 61.29.2 ([Tag
09C2](https://stacks.math.columbia.edu/tag/09C2)) gives $K=\Rlim K_n$ with
$K_n=K\otimes^L_\Lambda\underline{\Lambda/I^n}$ of tor amplitude in a fixed
interval $[a,b]$, with constructible cohomology sheaves and of the form
$K_n=\epsilon^{-1}L_n$ for $L_n\in D_{ctf}(X_{\Et},\Lambda/I^n)$. The
derived-tower bookkeeping itself is the blueprint's (the derived inverse
limit and the bounded constructible tower), and no entry makes the four
corner families objects of the derived tower category; the blueprint adds
the transition data, the compatibility of the rectangle with every
transition and with compatible endomorphisms of $K$, and the identification
of the $n$-th evaluations with the finite-level corners.

## Proof

The normalization isomorphisms of [def-weil-pbc-four-arrows] make the four
families strict towers, and the reduction compatibilities of the projection
formula and of the finite-level exchange map make the four arrows tower
morphisms; the rectangle equation of [lem-weil-pbc-finite-level-rectangle]
is then compatible with the transitions by construction.
