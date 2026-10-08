+++
id = "lem-fin-dense-normal-open"
kind = "lemma"
title = "A dense normal open in an integral finite-type scheme"
order = 1905
uses = ["def-fin-normalization-extension", "def-sbc-normal-dominant-galois", "def-weil-pbc-scheme-conventions", "lem-fin-normalization-extension-finite"]
+++
Every integral finite-type scheme over a field has a nonempty
open subscheme
which is normal.

## Proof

Choose a nonempty affine open $\operatorname{Spec}B$ and
take its normalization in its own fraction field, using
[def-fin-normalization-extension].
By [lem-fin-normalization-extension-finite], the
integral closure $C$ is a finite $B$-module. Express
its finitely many module generators as fractions in
$\operatorname{Frac}B$. A common nonzero denominator
$b\in B$ gives $C_b=B_b$. Since the integral closure
is integrally closed and localization preserves this
property, $B_b$ is a normal domain, as required by
[def-sbc-normal-dominant-galois]. The nonempty open
$\operatorname{Spec}B_b$ is dense because $X$ is integral.
