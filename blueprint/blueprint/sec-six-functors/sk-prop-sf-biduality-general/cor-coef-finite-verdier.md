+++
id = "cor-coef-finite-verdier"
kind = "theorem"
title = "Finite reductions of Verdier duality"
order = 2142
tags = ["latex:corollary"]
uses = ["lem-coef-finite-dualizing", "lem-weil-duality-pairing", "lem-weil-verdier-preservation-strata", "thm-coef-finite-hom"]
+++
For every $K\in D^b_{ctf}(X,A)$, there is a natural isomorphism

$$
d_{K,A,B}:(D_{X,A}K)\otimes_A^LB
\xrightarrow{\sim}D_{X,B}(K_B).
$$

The maps form a cocycle under further coefficient change and
carry evaluation and the double-dual morphism to the corresponding
maps at $B$. If $\dim X\leq d$ and $K$ has Tor interval
$[a,b]$, both sides have Tor interval $[-b-2d,-a]$.

## Proof

Apply [thm-coef-finite-hom] with second argument
$\omega_{X,A}$, and then use
[lem-coef-finite-dualizing] on that argument. The resulting
map is $d_{K,A,B}$. Evaluation compatibility follows from
the two comparisons already proved, and transposing evaluation
as in [lem-weil-duality-pairing] gives double-dual
compatibility. The cocycle is their quotient cocycle. The Tor
bound is [lem-weil-verdier-preservation-strata], together
with preservation of the Tor interval by scalar extension.
