+++
id = "lem-kun-closed-point-field"
kind = "lemma"
title = "Residue fields of closed points"
order = 1694
uses = ["def-kun-separably-closed", "def-kun-support", "def-weil-pbc-scheme-conventions", "lem-kun-sep-closed-finite-extension-purely-inseparable", "lem-kun-sep-closed-finite-extension-sep-closed"]
+++
Let $X$ be a scheme of
finite type over a field
$K$, and let $x\in X$.

1. **(a)** $x$ is a closed point of
$X$ if and only if
$\operatorname{trdeg}_K\kappa(x)=0$, i.e. if and only if
$\kappa(x)$ is finite over $K$ (Zariski's lemma: a field
finitely generated, as an algebra, over $K$ is finite over $K$).
1. **(b)** If $K$ is separably closed and $x$ is closed, then
$\kappa(x)/K$ is finite and purely inseparable and $\kappa(x)$ is
separably closed.

## Proof

For (a), the question is local, so replace $X$ by an affine
$\Spec(A)$ around $x$, $A$ a finitely generated $K$-algebra, and
$x=\mathfrak p$: $\mathfrak p$ is maximal in $A$ iff
$A/\mathfrak p$ is a field finitely generated as a $K$-algebra, and
by Zariski's lemma this is equivalent to $A/\mathfrak p$ being
finite over $K$ (then it has Krull dimension $0$, hence
$\operatorname{trdeg}_K=0$ by Noether normalization; conversely
finite implies dimension $0$ and hence maximality of $\mathfrak p$).
For (b), $\kappa(x)$ is finite over $K$ by (a), hence purely
inseparable by
[lem-kun-sep-closed-finite-extension-purely-inseparable]; thus
$\kappa(x)$ is a finite extension of the separably closed field
$K$ ([def-kun-separably-closed]) and is therefore separably
closed by [lem-kun-sep-closed-finite-extension-sep-closed].
