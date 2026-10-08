+++
id = "lemma-nagata-spectral-constructible-separation-exists"
kind = "lemma"
title = "Existence of constructible closed separators in a spectral space"
order = 252
lean = ["PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ"]
+++
If $T,T'$ are disjoint closed subsets of a spectral space $V$, there exist
quasi-compact opens $W,W'\subseteq V$ such that

$$
T'\subseteq W,\quad W\cap T=\varnothing,\quad
V\setminus W\subseteq W',\quad W'\cap T'=\varnothing.
$$

## Proof

Quasi-compact opens form a basis of a spectral space. For each $x\in T'$,
choose a quasi-compact open neighbourhood contained in $V\setminus T$.
The closed subset $T'$ is quasi-compact, so finitely many suffice; their
union is a quasi-compact open $W$ containing $T'$ and disjoint from $T$.
The closed subset $V\setminus W$ is quasi-compact and lies in the open
$V\setminus T'$. Cover it by finitely many quasi-compact opens contained
in $V\setminus T'$ and let $W'$ be their union.
