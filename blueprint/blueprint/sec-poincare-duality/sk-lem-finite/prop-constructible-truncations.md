+++
id = "prop-constructible-truncations"
kind = "theorem"
title = "Construction of constructible truncations"
order = 2432
tags = ["latex:proposition"]
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-finite-torsion-constructibility", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "def-weil-t-structure", "prop-weil-pbc-integral-tstructure", "thm-weil-pbc-integral-truncations"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$. Fix a prime $\ell\neq p$, write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and
choose a finite extension $E/\Ql$ contained in $\Qlb$. Let $Y$ be a
finite-type $k$-scheme, where
finite type is the scheme
condition used throughout. Let
$\Lambda\in\{E,\Qlb\}$. For $\Lambda=E$, let
$D^b_c(Y,E)$ be the
rationalized
category obtained
from integral complexes whose finite-level reductions satisfy the
finite-torsion
constructibility condition; for $\Lambda=\Qlb$, use the
common finite-stage
coefficient construction. The symbols $\mathcal H^r$ denote the
cohomology sheaves of a
derived complex. Let $m,i\in\mathbf Z$.
There are truncation functors

$$
\tau^{\leq m},\tau^{\geq m}:D^b_c(Y,\Lambda)
\longrightarrow D^b_c(Y,\Lambda).
$$

At a common finite coefficient field they are the
standard truncations of the
constructible derived category; they commute with finite scalar extension and
with the transitions of the coefficient tower.
For $\Lambda=E$ or $\Qlb$, these truncations, their natural maps, and the
distinguished truncation triangles satisfy the axioms of a
bounded t-structure. For
$K\in D^b_c(Y,\Lambda)$, define its cohomology functors by

$$
\mathcal H^i(K)=\bigl(\tau^{\geq i}\tau^{\leq i}K\bigr)[i].
$$

For every scheme automorphism $h:Y\xrightarrow{\sim}Y$, the
derived pullback $Lh^*$
commutes with the truncations and with $\mathcal H^i$.

## Proof

At a finite coefficient stage the truncation functors of the
t-structure of [def-weil-derived-cohomology-sheaves] are the
canonical truncations of complexes, computed levelwise; they are exact
triangulated on the bounded constructible derived category, because the
truncation of a bounded constructible complex has the cohomology sheaves
of the original complex in the surviving degrees, hence satisfies the
finite-torsion constructibility condition in the same finite partition.
At the derived-complete integral level, the truncations are the
levelwise ones on the reduction tower of
[thm-weil-pbc-integral-truncations] of the proper-base-change chapter, and the
standard t-structure restricts to the integral category by
[prop-weil-pbc-integral-tstructure] of the proper-base-change chapter.
The canonical truncation triangles give the axioms of a bounded
t-structure in the sense of [def-weil-t-structure]. Being
characterized by the vanishing of cohomology sheaves,
the truncations commute with finite scalar extension and with the
transitions of the coefficient tower, so they descend to the rationalized
category of
[def-weil-rationalization-karoubi] and to the common-stage
category of [def-weil-algebraically-closed-coefficients], where
the truncation triangles give the same bounded t-structure axioms; the
displayed definition of $\mathcal H^i$ is then the canonical
identification. For a scheme automorphism $h$, the derived pullback
$Lh^*$ of [def-weil-derived-pullback-tensor-hom] is exact
triangulated, so it commutes with the canonical truncations and hence
with $\mathcal H^i$.

*Recorded in advance* from chapter *Verification of the operations and cohomological interfaces* of the source.
