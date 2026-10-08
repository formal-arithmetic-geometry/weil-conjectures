+++
id = "lemma-nagata-localization-ideal-pow"
kind = "lemma"
title = "Localization commutes with powers of an ideal"
order = 37
lean = ["Ideal.map_pow"]
+++
Let $s\in A$. For every $n$ there is a canonical equality

$$
(I^n)A_s=(IA_s)^n.
$$

## Proof

Extension of ideals along a ring homomorphism preserves products and the
unit ideal. Induct on $n$.
