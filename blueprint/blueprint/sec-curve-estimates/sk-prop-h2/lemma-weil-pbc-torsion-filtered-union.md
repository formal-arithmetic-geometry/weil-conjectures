+++
id = "lemma-weil-pbc-torsion-filtered-union"
kind = "lemma"
title = "Filtered torsion union"
order = 954
uses = ["def-weil-pbc-etale-sheaves"]
+++
For every torsion sheaf $F$ the inclusions $F[n]\hookrightarrow F[mn]$ form a
filtered system and the canonical map $\varinjlim_nF[n]\to F$ is an
isomorphism.

## Proof

The transition map sends a section killed by $n$ to the same section, now
regarded as killed by $mn$. The map to $F$ is monic because a section that is
zero in $F$ is already zero in every $F[n]$. It is epic because every local
section of $F$ is locally killed by some positive integer and hence is locally in one
of the $F[n]$; sheafification preserves this local epimorphism.

## Detailed form

For every torsion sheaf [def-weil-pbc-etale-sheaves] $F$ on $X_{\Et}$,

$$
 F=\varinjlim_{(\mathbf N_{>0},\mid)}F[n],\qquad
 F[n]=\ker(n:F\to F),
$$

as a filtered colimit in $\Ab(X_{\Et})$. Here positive integers are ordered
by divisibility, and for $n\mid m$ the transition map is the inclusion
$F[n]\hookrightarrow F[m]$; this poset is filtered because
$\operatorname{lcm}(n,m)$ is a common upper bound.

## Proof

Every local section of $F$ is locally killed by some positive integer, hence lies in
$F[n]$ locally, so the canonical map to $F$ is an epimorphism of sheaves; a
section that is zero in $F$ is already zero in every $F[n]$, so it is a
monomorphism. Filteredness follows from the lcm property, and the sheaf
axioms pass the local statements to global ones, exactly in the sense of
[def-weil-pbc-etale-sheaves].
