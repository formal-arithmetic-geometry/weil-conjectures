+++
id = "def-nagata-spectral-constructible-separation"
kind = "definition"
title = "Constructible separation data in a spectral space"
order = 253
uses = ["lemma-nagata-spectral-constructible-separation-exists"]
+++
**Status.** Bypassed by the formalized route: the existence statement
`PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ`
is used directly, so no selected separation datum and specification lemma
are introduced.

Let $T,T'\subseteq V$ be disjoint closed subsets of a spectral space.
Select quasi-compact opens $(W,W')$ from
[lemma-nagata-spectral-constructible-separation-exists] and define

$$
T_c=V\setminus W,
\qquad
T'_c=V\setminus W'.
$$
