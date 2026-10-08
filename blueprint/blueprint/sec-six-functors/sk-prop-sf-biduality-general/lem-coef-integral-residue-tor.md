+++
id = "lem-coef-integral-residue-tor"
kind = "lemma"
title = "The residue reduction controls integral Tor amplitude"
order = 2133
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-finite-tor-amplitude", "lem-exc-residue-tor-test"]
+++
Let $K\in D^b_c(X,R)$ in the actual sense of
[def-weil-derived-complete-integral-detailed]. If $K_1$ has
cohomology in $[a,b]$, then every $K_n$ has Tor amplitude
in $[a,b]$. Consequently

$$
D^b_c(X,R)=D^b_{ctf}(X,R)
$$

for this DVR coefficient category. This assertion does not equate
constructibility with site-perfectness on the whole scheme.

## Proof

Associativity of coefficient tensor product gives
$K_n\otimes^L_{A_n}\kappa=K_1$.
Each $K_n$ is bounded constructible by
[def-weil-derived-complete-integral-detailed]. The residue Tor test
[lem-exc-residue-tor-test], applied to the local Artinian
ring $A_n$, therefore gives the same Tor interval $[a,b]$
at every $n$. This is precisely the integral condition in
[def-weil-finite-tor-amplitude]. The reverse inclusion is
part of that definition.
