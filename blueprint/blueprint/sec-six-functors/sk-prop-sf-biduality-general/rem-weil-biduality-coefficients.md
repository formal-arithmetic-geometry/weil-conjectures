+++
id = "rem-weil-biduality-coefficients"
kind = "remark"
title = "Ordinary, derived, and geometric biduality"
order = 2121
uses = ["def-weil-finite-torsion-constructibility", "lem-weil-coefficient-frobenius"]
+++
For $R=\mathcal O_E$ and $T=R/\varpi_E R$, ordinary duality gives
$T^*=0$, whereas the resolution
$0\to R\xrightarrow{\varpi_E}R\to T\to0$ gives

$$
R\operatorname{Hom}_R(T,R)\cong T[-1],\qquad
R\operatorname{Hom}_R\bigl(R\operatorname{Hom}_R(T,R),R\bigr)\cong T.
$$

These identifications use the chosen uniformizer; the derived evaluation
is canonical and is an isomorphism by
[lem-weil-coefficient-frobenius]. Computing two ordinary Hom modules
over a non-self-injective ring does not compute two derived Homs.

For the bounded constructible finite-Tor category of
[def-weil-finite-torsion-constructibility], the algebraic point case
uses perfect derived biduality and does not need a quasi-Frobenius ring.
Self-injectivity of $A_{E,n}$ also provides ordinary duality for finite
modules that need not have finite Tor dimension; this distinction is
relevant to the stronger bounded constructible category without the
finite-Tor condition. Neither algebraic assertion alone proves geometric
Verdier biduality across the boundary of a stratum: restriction along a
closed immersion cannot be treated as restriction along an open immersion.
