+++
id = "lem-a1-spectrum-exact-sequence"
kind = "lemma"
title = "Spectrum of an exact Frobenius sequence"
order = 2732
uses = ["def-weil-frobenius-module-weights", "p-linear-filtration"]
+++
For a short exact sequence $0\to V'\to V\to V''\to0$ of finite
Frobenius modules whose maps commute with Frobenius, the spectrum of
$(V,F)$ (the multiset of the images under $\iota$ of the
eigenvalues, [def-weil-frobenius-module-weights]) is the multiset
union of the spectra of $V'$ and $V''$, counted with algebraic
multiplicity.

## Proof

Choose a basis of $V'$ and complete it to a basis of $V$; the Frobenius
matrix of $V$ is upper block triangular with diagonal blocks the
Frobenius matrices of $V'$ and $V''$, in the sense of
[def-weil-frobenius-module-weights]. Hence the characteristic
polynomial satisfies $\chi_V(T)=\chi_{V'}(T)\chi_{V''}(T)$ ([p-linear-filtration]), and taking
orders of vanishing at each root shows the algebraic multiplicities add.
