+++
id = "prop-weil-pbc-composition-stability"
kind = "theorem"
title = "Composition stability"
order = 1195
uses = ["def-weil-pbc-injective-acyclicity-property", "def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-direct-image-preserves-injectives", "lem-weil-pbc-grothendieck-spectral-sequence", "lemma-weil-pbc-proper-underived-exchange", "lemma-weil-pbc-property-iff-acyclicity"]
tags = ["latex:proposition"]
+++
Let $X\xrightarrow{f}Y\xrightarrow{h}Z$ be proper. If $\mathrm{IA}(f)$ and
$\mathrm{IA}(h)$ hold, then $\mathrm{IA}(hf)$ and hence $\mathrm{PBC}(hf)$
hold.

## Proof

After an arbitrary base change $c:Z'\to Z$, write $Y'=Y\times_ZZ'$,
$X'=X\times_ZZ'$, with projections $b:Y'\to Y$ and $a:X'\to X$, and
base-changed maps $f'$, $h'$. Let $I$ be injective in $\mathbf F_r$-module
sheaves on $X$. By [lem-weil-pbc-direct-image-preserves-injectives] the sheaf
$f_*I$ is injective on $Y$. $\mathrm{IA}_r(f)$ gives $R^qf'_*a^{-1}I=0$ for
$q>0$, and the underived proper exchange identifies $f'_*a^{-1}I\cong
b^{-1}f_*I$; $\mathrm{IA}_r(h)$ applied to the injective $f_*I$ makes this
sheaf $h'_*$-acyclic. The Grothendieck spectral sequence of
[lem-weil-pbc-grothendieck-spectral-sequence] therefore vanishes in every
positive total degree, giving $\mathrm{IA}_r(hf)$, and $\mathrm{PBC}(hf)$ by
the equivalence between $\mathrm{PBC}$ and $\mathrm{IA}$ recorded with
[def-weil-pbc-property].
