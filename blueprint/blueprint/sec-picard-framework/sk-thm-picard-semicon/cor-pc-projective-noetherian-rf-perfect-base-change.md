+++
id = "cor-pc-projective-noetherian-rf-perfect-base-change"
kind = "theorem"
title = "Arbitrary base change for a projective Noetherian family"
order = 674
tags = ["latex:corollary"]
uses = ["def-pc-base-change", "def-pc-derived-direct-image", "def-pc-derived-pullback", "def-pc-morphism-conventions", "def-pc-perfect-complex", "def-pc-projective-morphism", "lem-pc-projective-noetherian-rf-perfect", "lem-pc-rf-base-change-flat-module", "pqf-def-coherent"]
+++
Let $S$ be locally Noetherian, let $f:X\to S$ be
projective, and let
$\mathcal G$ be a coherent
$\mathcal O_X$-module flat over $S$.
For any morphism $g:T\to S$, without a Noetherian hypothesis on
$T$, the canonical base-change map

$$
Lg^*(Rf_*\mathcal G)\longrightarrow Rf_{T,*}\mathcal G_T
$$

is an isomorphism, and both sides are perfect.
The symbols $Lg^*$ and $Rf_*$ denote the
derived pullback and
derived direct image.

## Proof

The isomorphism is [lem-pc-rf-base-change-flat-module].
By [lem-pc-projective-noetherian-rf-perfect], the source
before pullback is perfect. Locally it is a bounded complex of
finite projective modules, as in [def-pc-perfect-complex].
Tensoring such a complex with any base algebra preserves this
description: a finite projective module is the image of an
idempotent on a finite free module, and tensoring preserves that
idempotent decomposition. Hence derived pullback is perfect,
and the isomorphic right side is perfect as well.
