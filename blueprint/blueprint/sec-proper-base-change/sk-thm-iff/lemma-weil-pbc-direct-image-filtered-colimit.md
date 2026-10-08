+++
id = "lemma-weil-pbc-direct-image-filtered-colimit"
kind = "lemma"
title = "Filtered colimits and higher direct image"
order = 1087
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-cohomology-filtered-colimit", "lem-weil-pbc-qcqs-higher-direct-image"]
+++
For a quasi-compact and quasi-separated morphism of schemes $h:W\to V$ and a
filtered system of torsion sheaves $(F_i)$, the canonical map

$$
\varinjlim_i R^qh_*F_i\longrightarrow R^qh_*(\varinjlim_iF_i)
$$

is an isomorphism for every $q$.

## Proof

For $q=0$, sections on a quasi-compact etale object are the equalizer of a
finite covering diagram after a finite quasi-compact refinement; filtered
colimits commute with this finite limit. For $q>0$, represent a class by a
degree-$q$ cocycle on a split etale hypercover with finite $(q+1)$-skeleton.
Each of its finitely many sections is represented in some $F_i$, and the
finite list of face-map equalities holds at one later index because the system
is filtered. This proves surjectivity of
$\varinjlim_iH^q(W,F_i)\to H^q(W,\varinjlim_iF_i)$.

If a class from $F_i$ dies after the colimit, choose a finite hypercover
refinement and a degree-$(q-1)$ null-homotopy on the limit. Its finitely many
sections, refinement maps, and equations descend to one index $j\geq i$;
there the class is already a coboundary. Thus the map is injective. The
same argument applies after every quasi-compact etale base change
$U\to V$, so the cohomology-sheaf description of $R^qh_*$ identifies the
displayed sheaves. This is the derived filtered-colimit argument, with no
unbounded injective replacement required.

## Detailed form

If $u:U\to V$ is quasi-compact and quasi-separated
[def-weil-pbc-scheme-conventions] and $(F_i)$ is a filtered system of torsion
etale sheaves [def-weil-pbc-etale-sheaves], then for every $q\geq0$ the
canonical map

$$
 \varinjlim_iR^qu_*F_i\xrightarrow{\sim}R^qu_*(\varinjlim_iF_i)
$$

involving the higher direct image [def-weil-pbc-direct-image] is an
isomorphism. The same assertion holds after arbitrary base change.

## Proof

The higher direct image of [def-weil-pbc-direct-image] is the sheafification
of $W\mapsto H^q(W\times_VU,F|)$ by
[lem-weil-pbc-qcqs-higher-direct-image], the morphism $u$ being quasi-compact
and quasi-separated.

Use the basis of affine etale $W\to V$. Then $W\times_VU$ is quasi-compact
and quasi-separated, so [lem-weil-pbc-cohomology-filtered-colimit] applies to
the displayed presheaf on every basis object. Inverse image to $W\times_VU$
commutes with filtered colimits. Finally, sheafification preserves colimits,
and filtered colimits are exact. Sheafifying the resulting isomorphisms
proves the assertion. Quasi-compactness and quasi-separatedness are preserved
by base change, so this argument also proves the last sentence.
