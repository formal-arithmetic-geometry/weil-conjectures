+++
id = "lemma-weil-pbc-five-lemma-transfer"
kind = "lemma"
title = "Five-lemma transfer for exchange"
order = 1089
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-etale-sheaves", "lemma-weil-pbc-derived-exchange-replacement", "lemma-weil-pbc-prime-factor-induction"]
+++
In a short exact sequence of torsion sheaves, if two of the three derived
exchange maps are isomorphisms, then the third is an isomorphism.

## Proof

Apply $g^{-1}Rf_*$ and $Rf'_*g'^{-1}$ to the short exact sequence and write
the natural long exact cohomology sequences. Naturality of the exchange map
gives a morphism between these sequences. In each degree the five-lemma
applies to the five adjacent terms, with the boundary maps identified by the
connecting-homomorphism construction from an injective resolution. Thus the
middle exchange map is an isomorphism in every degree.

## Detailed form

For a short exact sequence $0\to F_1\to F\to F_2\to0$ of torsion sheaves
[def-weil-pbc-etale-sheaves], the exchange transformations of
[def-weil-pbc-derived-exchange] form a morphism between the two long
exact sequences of higher direct images. If exchange is an isomorphism for
$F_1$ and $F_2$ in every degree, then it is an isomorphism for $F$ in every
degree.

## Proof

Applying $g^{-1}Rf_*$ and $Rf'_*g'^{-1}$ to the short exact sequence produces
two long exact cohomology sequences. Naturality of the derived exchange
morphism in the sheaf, as in
[lemma-weil-pbc-derived-exchange-replacement], makes the exchange maps a
morphism between these sequences, with the boundary maps identified by the
connecting-homomorphism construction from an injective resolution of
[def-weil-pbc-derived-exchange]. In each degree the five lemma
applies to the five adjacent terms, so the middle exchange map is an
isomorphism in every degree.
