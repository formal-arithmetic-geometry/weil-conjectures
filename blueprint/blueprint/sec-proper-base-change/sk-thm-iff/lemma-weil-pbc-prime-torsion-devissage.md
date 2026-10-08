+++
id = "lemma-weil-pbc-prime-torsion-devissage"
kind = "lemma"
title = "Prime-torsion devissage"
order = 1090
uses = ["lemma-weil-pbc-direct-image-filtered-colimit", "lemma-weil-pbc-five-lemma-transfer", "lemma-weil-pbc-prime-factor-induction", "lemma-weil-pbc-torsion-filtered-union"]
+++
For a torsion sheaf $F$, write $F[n]=\ker(n:F\to F)$. Then
$F=\varinjlim_nF[n]$; for $m\mid n$ the inclusion $F[m]\subseteq F[n]$
is monic, and if $n=\prod_i\ell_i^{e_i}$, repeated use of

$$
0\longrightarrow F[\ell_i]\longrightarrow F[n]
\xrightarrow{\ell_i}\ell_iF[n]\longrightarrow0
$$

reduces assertions about $F[n]$ to assertions about $\ell_i$-torsion.

## Proof

The filtered union is Lemma [lemma-weil-pbc-torsion-filtered-union].
The exact sequence is the kernel–image sequence for multiplication by
$\ell_i$, since the kernel in $F[n]$ is $F[\ell_i]$. Lemma [lemma-weil-pbc-prime-factor-induction] and the
five-lemma transfer then prove the assertion for every $F[n]$, and
Lemma [lemma-weil-pbc-direct-image-filtered-colimit] passes to $F$.
