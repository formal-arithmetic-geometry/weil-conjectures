+++
id = "lem-fin-normalization-extension-finite"
kind = "lemma"
title = "Finiteness of normalization in a finite extension"
order = 1015
uses = ["def-fin-normalization-extension", "def-weil-pbc-scheme-conventions"]
+++
For an integral scheme $X$ of finite type over a field
and a finite extension of its function field, the map of
[def-fin-normalization-extension] is
finite.

## Proof

For $X=\operatorname{Spec}B$, the finite-normalization
theorem of commutative algebra says that the integral
closure of a finitely generated domain over a field in
any finite extension of its fraction field is a finite
$B$-module. This is the Nagata-ring theorem for
finite-type field algebras, recorded in
[Stacks
Project, Section 29.18](https://stacks.math.columbia.edu/tag/0359); we use this commutative-algebra
theorem as a foundational input. Apply it to the affine
algebras in [def-fin-normalization-extension].
Their relative spectra are finite over the corresponding
affine opens, which is precisely finiteness in
[def-weil-pbc-scheme-conventions]. The localization
identifications in the construction glue these finite maps.
