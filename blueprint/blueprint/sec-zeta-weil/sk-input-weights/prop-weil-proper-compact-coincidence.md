+++
id = "prop-weil-proper-compact-coincidence"
kind = "theorem"
title = "Proper coincidence of compact-support and ordinary cohomology"
order = 2871
tags = ["latex:proposition"]
uses = ["def-compact-support-direct-image-detailed", "def-weil-derived-direct-image", "def-weil-ordinary-compact-cohomology", "def-weil-scheme-morphism-properties"]
+++
In the notation of
[def-weil-ordinary-compact-cohomology], if $Y$ is
proper then the
compact-support direct image and the ordinary direct image agree,

$$
Ra_{Y!}\cong Ra_{Y*},
$$

so that $H_c^i(Y,K)\cong H^i(Y,K)$ for every $K$. (This is
$\Cref{def-compact-support-direct-image-detailed}$ and
[def-weil-derived-direct-image] applied to a proper structure
morphism, and the exchange criterion of the proper base-change theorem
for the identity base change.)

## Proof

If $Y$ is proper, the identity is a compactification of the structure
morphism $a_Y$, namely
$Y\xrightarrow{\operatorname{id}}Y\xrightarrow{a_Y}\Spec k$
with $a_Y$ proper, so at every finite coefficient level
$Ra_{Y!,n}=Ra_{Y*,n}$ by
[def-compact-support-direct-image-detailed], and the comparison maps of
that definition are identities for the identity refinement; hence the
compactification-independent functor $Ra_{Y!}$ is naturally
identified with the ordinary derived direct image $Ra_{Y*}$ of
[def-weil-derived-direct-image]. Applying the equivalence
$\operatorname{Fib}_s$ of
[def-weil-ordinary-compact-cohomology] to both sides gives
$\RGammac(Y,K)\cong\RGamma(Y,K)$, hence
$H_c^i(Y,K)\cong H^i(Y,K)$ for every $K$, by the definitions of the
ordinary and compactly supported cohomology groups in
[def-weil-ordinary-compact-cohomology].
