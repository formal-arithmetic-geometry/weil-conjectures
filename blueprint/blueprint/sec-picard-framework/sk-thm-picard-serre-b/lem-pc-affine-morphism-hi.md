+++
id = "lem-pc-affine-morphism-hi"
kind = "lemma"
title = "Higher direct images of affine morphisms"
order = 623
uses = ["def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-vanishing"]
+++
Let $f:X\to S$ be an affine morphism and $\mathcal{F}$ a quasi-coherent
$\mathcal{O}_X$-module. Then $R^if_*\mathcal{F}=0$ for all $i>0$, and $f_*\mathcal{F}$ is
quasi-coherent.

## Proof

The higher direct images commute with restriction to open subschemes
(of the target), and for an affine open $V\subseteq S$ the preimage
$f^{-1}(V)$ is affine (definition of an affine morphism). Hence, on a
basis of affine opens $V$ of $S$, the sections of $R^if_*\mathcal{F}$ are
$H^i(f^{-1}(V),\mathcal{F}|)=0$ by [lem-pc-affine-vanishing]; so
$R^if_*\mathcal{F}=0$ for $i>0$, and $f_*\mathcal{F}$ is quasi-coherent since its
value on $V$ is $\Gamma(f^{-1}(V),\mathcal{F})^{\sim}$.
