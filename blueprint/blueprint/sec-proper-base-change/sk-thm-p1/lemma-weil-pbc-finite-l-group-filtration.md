+++
id = "lemma-weil-pbc-finite-l-group-filtration"
kind = "lemma"
title = "Finite $\\ell$-group representation filtration"
order = 1144
+++
Let $H$ be a finite $\ell$-group and $V$ a nonzero finite-dimensional
$\mathbf F_\ell[H]$-module. Then $V^H\ne0$ and $V$ has a finite filtration
by $H$-stable subspaces whose successive quotients are the trivial
one-dimensional representation.

## Proof

The group algebra augmentation ideal $J\subset\mathbf F_\ell[H]$ is nilpotent:
induct on $|H|$, choose a central subgroup $C$ of order $\ell$, and use
$(c-1)^\ell=c^\ell-1=0$ together with nilpotence for $H/C$. Choose the least
$r$ with $J^rV=0$; then $J^{r-1}V$ is nonzero and fixed by $H$. Select a
one-dimensional fixed subspace and induct on $\dim V$ after quotienting by it.
This fills the future-reference gap in Tag `0A3R`.

## Detailed form

Let $H$ be a finite $r$-group and let $V$ be a nonzero finite-dimensional
$\mathbf F_r[H]$-module. Then $V^H\neq0$, and $V$ has an $H$-stable finite
filtration whose successive quotients are the trivial one-dimensional
representation.

## Proof

The augmentation ideal of $\mathbf F_r[H]$ is nilpotent, so the fixed subspace
$V^H$ is nonzero; induction on $\dim_{\mathbf F_r}V$ using the exact sequence
$0\to V^H\to V\to V/V^H\to0$ gives the filtration.
