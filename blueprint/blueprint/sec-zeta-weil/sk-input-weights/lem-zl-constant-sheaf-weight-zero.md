+++
id = "lem-zl-constant-sheaf-weight-zero"
kind = "lemma"
title = "Weight zero of the constant sheaf"
order = 2872
uses = ["def-weil-global-geometric-frobenius", "def-weil-local-frobenius-trace", "def-weil-punctual-weights", "def-weil-weil-sheaf-complex"]
+++
On every separated finite-type $k_0$-scheme, the constant
Weil sheaf $\Qlb$ is
punctually $\iota$-pure of weight zero.

## Proof

At a degree-$n$ closed point, the local Frobenius operator of
[def-weil-local-frobenius-trace] acts on the constant stalk by
identity (the $n$-fold iterate of the geometric Frobenius of
[def-weil-global-geometric-frobenius] fixes the constant section
$1$), whose complex absolute value is $1=q^{n\cdot0/2}=q_y^{0/2}$
as required by [def-weil-punctual-weights].
