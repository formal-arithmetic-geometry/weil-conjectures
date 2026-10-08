+++
id = "ex-exc-excision-is-not-the-comparison"
kind = "remark"
title = "The excision comparison is not the base-change comparison"
order = 1816
tags = ["latex:example"]
uses = ["def-weil-extension-by-zero", "def-weil-pbc-direct-image", "prop-exc-ambient-dual-base-change"]
+++
The comparison $Lg'^*Rf^{\times}\to Rf'^{\times}Lg^*$ of
[prop-exc-ambient-dual-base-change] is *not* equivalent to the
excision comparison $Rf_!(g'_!\to g'_*)$ for an open immersion $g$:
the former can be an isomorphism while the latter is not.

## Proof

Take $f=\operatorname{id}_Y$ on a smooth curve $Y$, and let
$g:Y'\hookrightarrow Y$ be the complement of a closed point, so that
$X=Y$, $X'=Y'$, $g'=g$ and $f'=\operatorname{id}_{Y'}$. The
identity functor has right adjoint itself, so both sides of
$Lg'^*Rf^{\times}\to Rf'^{\times}Lg^*$ are $Lg^*$ and the comparison
is the identity, an isomorphism. On the other hand
$Rf_!(g'_!\to g'_*)$ is $g_!\to g_*$, and the
[def-weil-extension-by-zero] comparison is not an isomorphism: at
the closed point the stalk of $g_*\Lambda_{Y'}$ is
$\Lambda$ by the [def-weil-pbc-direct-image] description of
direct images, while $g_!\Lambda_{Y'}$ has zero stalk there. Hence the
two statements are not equivalent.
