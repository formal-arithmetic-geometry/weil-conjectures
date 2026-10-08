+++
id = "lem-weil-pbc-zero-dimensional-field-extension"
kind = "lemma"
title = "Field extension in dimension zero"
order = 1152
uses = ["def-weil-pbc-curve-setting", "def-weil-pbc-eight-curve-assertions", "lem-weil-pbc-zero-dimensional-cohomology", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Let $k\subset k'$ be algebraically closed fields, let $C$ be a separated
finite-type $k$-scheme of dimension at most zero, and let $F$ be a torsion
etale sheaf. The pullback map $\rho^q_{k'/k}(C,F)$ of the curve coefficient
pair [def-weil-pbc-curve-setting] is an isomorphism for every $q\geq0$.

## Proof

By [lem-weil-pbc-zero-dimensional-cohomology], both sides vanish for $q>0$. In
degree zero, reduce by invariance under universal homeomorphisms to the finite
disjoint union $C_{\mathrm{red}}=\coprod_c\operatorname{Spec}k$; its base
change is $\coprod_c\operatorname{Spec}k'$. On each point the pullback of a
sheaf of abelian groups is the same group, and its map on sections is the
identity. The map $\rho^0_{k'/k}(C,F)$ of
[def-weil-pbc-eight-curve-assertions] is therefore the product of
these identity maps, hence an isomorphism.
