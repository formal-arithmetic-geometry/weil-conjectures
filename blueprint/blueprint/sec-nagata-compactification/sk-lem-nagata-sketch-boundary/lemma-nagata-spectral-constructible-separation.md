+++
id = "lemma-nagata-spectral-constructible-separation"
kind = "lemma"
title = "Properties of the constructible separation data"
order = 254
uses = ["def-nagata-spectral-constructible-separation", "lemma-nagata-spectral-constructible-separation-exists"]
+++
**Status.** Bypassed by the formalized route: the existence statement
`PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ`
is used directly, so no selected separation datum and specification lemma
are introduced.

The constructed subsets $T_c,T'_c$ are constructible and closed in $V$,
and they satisfy

$$
T\subseteq T_c,\qquad T'\subseteq T'_c,\qquad
T_c\cap T'_c=\varnothing.
$$

## Proof

Complements of quasi-compact opens in a spectral space are constructible
closed subsets. The choice of $W$ gives $T\subseteq T_c$, the choice of
$W'$ gives $T'\subseteq T'_c$, and $V\setminus W\subseteq W'$ gives
$T_c\cap T'_c=\varnothing$.
