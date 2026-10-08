+++
id = "lem-sc-cd-affine-limit"
kind = "lemma"
title = "Passing a uniform torsion bound to an affine limit"
order = 1547
uses = ["def-sc-etale-torsion-cd", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-cohomology-filtered-colimit", "lemma-weil-pbc-etale-cohomology-continuity", "lemma-weil-pbc-torsion-filtered-union"]
+++
Let $X=\varprojlim_i X_i$ be a filtered inverse limit of
quasi-compact
quasi-separated schemes with affine transition maps.
If $\operatorname{cd}_{\rm tor}(X_i)\leq c$ for every $i$,
then $\operatorname{cd}_{\rm tor}(X)\leq c$, with bounds as in
[def-sc-etale-torsion-cd].

## Proof

Let $p_i:X\to X_i$, and first let $F$ be killed by a fixed
integer $n>0$. Set $F_i=p_{i*}F$; for $j\geq i$
the adjunction maps give transition arrows
$p_{ji}^*F_i\to F_j$, and hence arrows
$p_i^*F_i\to p_j^*F_j$ on $X$.
The canonical map $\varinjlim_i p_i^*F_i\to F$ is an
isomorphism. To verify it, use quasi-compact etale objects
of finite presentation: every such object and every morphism
between two of them descends to a stage of the inverse system.
A section of $F$ on a descended object is, by definition,
a section of $p_{i*}F$ on that object at stage $i$, proving
surjectivity locally. If two representatives agree after
pullback, their equality is witnessed on a finite etale covering;
the covering and the finitely many maps in it descend to a
later stage. This proves injectivity after sheafification.
These are the same finite-presentation descent and finite-cover
arguments used in [lemma-weil-pbc-etale-cohomology-continuity].

For each fixed $i$, that theorem gives

$$
H^q(X,p_i^*F_i)=\varinjlim_{j\geq i}
H^q(X_j,p_{ji}^*F_i)=0\quad(q>c).
$$

Now apply [lem-weil-pbc-cohomology-filtered-colimit] to
the preceding sheaf colimit. Finally remove the fixed exponent
using [lemma-weil-pbc-torsion-filtered-union] and the same
commutation of cohomology with filtered colimits.
