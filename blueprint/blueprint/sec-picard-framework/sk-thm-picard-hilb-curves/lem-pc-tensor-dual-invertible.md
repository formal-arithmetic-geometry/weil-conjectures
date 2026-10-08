+++
id = "lem-pc-tensor-dual-invertible"
kind = "lemma"
title = "Invertible modules: duals and tensor products"
order = 791
uses = ["def-pc-morphism-conventions", "def-pc-scheme", "def-sc-invertible-module"]
+++
Let $X$ be a scheme and let $\mathcal{M},\mathcal{N}$ be
invertible $\mathcal{O}_X$-modules. Then
$\mathcal{M}^\vee=\mathcal{H}om_{\mathcal{O}_X}(\mathcal{M},\mathcal{O}_X)$ is invertible, so is
$\mathcal{M}\otimes_{\mathcal{O}_X}\mathcal{N}$, and the canonical maps
$\mathcal{M}\otimes\mathcal{M}^\vee\to\mathcal{O}_X$ and $\mathcal{M}\to\mathcal{M}^{\vee\vee}$ are
isomorphisms.

## Proof

All three assertions are Zariski-local in $X$, and at a point $x$ an
invertible $\mathcal{O}_{X,x}$-module is free of rank $1$, hence isomorphic to
$\mathcal{O}_{X,x}$: then $\mathcal{M}^\vee\cong\mathcal{O}_x$, $\mathcal{M}\otimes\mathcal{N}\cong\mathcal{O}_x$,
$\mathcal{M}\otimes\mathcal{M}^\vee\cong\mathcal{O}_x$ and $\mathcal{M}\to\mathcal{M}^{\vee\vee}$ is the
identity of $\mathcal{O}_x$ (the canonical pairing is the multiplication map,
which is an isomorphism for free modules of rank $1$). Since
isomorphism is a local property of coherent modules, the claim follows.
