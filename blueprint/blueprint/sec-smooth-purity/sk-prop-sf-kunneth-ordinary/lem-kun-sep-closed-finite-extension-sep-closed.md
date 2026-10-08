+++
id = "lem-kun-sep-closed-finite-extension-sep-closed"
kind = "lemma"
title = "Finite extensions of a separably closed field are separably closed"
order = 1671
uses = ["def-kun-separably-closed", "lem-kun-sep-closed-finite-extension-purely-inseparable"]
+++
Let $K$ be a separably closed field and $L/K$ a finite field
extension. Then $L$ is separably closed.

## Proof

Let $M/L$ be a finite separable extension. Its maximal subfield
separable over $K$ is a finite separable extension of the separably
closed field $K$, hence equals $K$; so $M/K$ is purely
inseparable by
[lem-kun-sep-closed-finite-extension-purely-inseparable]. A
subextension of a purely inseparable extension is purely inseparable,
so $M/L$ is both purely inseparable and separable, hence trivial:
$M=L$. Therefore $L$ has no nontrivial finite separable
extension, that is, $L$ is separably closed by
[def-kun-separably-closed].
