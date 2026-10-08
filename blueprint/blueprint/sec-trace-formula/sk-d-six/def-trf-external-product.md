+++
id = "def-trf-external-product"
kind = "definition"
title = "External product on the square"
order = 2271
uses = ["def-trf-coefficient-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties"]
+++
Use the finite coefficient ring $A=A_{E,n}$. For finite-type $k$-schemes $X_1,X_2$, projections
$p_i:X_1\times_kX_2\to X_i$, and complexes
$M_i$ in the finite-Tor constructible category $D^b_{ctf}(X_i,A)$, define

$$
M_1\boxtimes_A^L M_2:=Lp_1^*M_1\otimes_A^L Lp_2^*M_2.
$$

This notation includes the order of the factors and uses only the derived
pullback and tensor of [def-weil-derived-pullback-tensor-hom] and
[def-weil-derived-tensor].
