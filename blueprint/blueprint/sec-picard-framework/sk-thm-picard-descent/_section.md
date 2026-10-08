+++
id = "sk-thm-picard-descent"
kind = "section"
title = "Descent"
order = 762
uses = ["sk-def-av-pic"]
lean = ["AlgebraicGeometry.bijective_toDescentData_map", "AlgebraicGeometry.exists_isQuasicoherent_toDescentData_iso", "AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso", "AlgebraicGeometry.isLocallyFree_of_toDescentData_iso", "AlgebraicGeometry.isInvertible_of_toDescentData_iso", "AlgebraicGeometry.isSheaf_fpqc_finiteLocallyFreeSubscheme"]
+++
*Theorem (sketch).*

Let $\{T_i\to T\}_{i\in I}$ be an fpqc covering.

1. ****(D1)**** *Descending modules.* Descent data for
quasi-coherent $\cO$-modules on the covering are effectively
represented by quasi-coherent $\cO_T$-modules; the equivalence
preserves and reflects flatness, finite presentability and finite
local freeness (of a given rank); local freeness of infinite rank is
*not* fpqc-local (Stacks
[05VF](https://stacks.math.columbia.edu/tag/05VF)). In
particular: *descent of invertible modules* — cartesian
isomorphisms $\cL_i$'s satisfying the cocycle condition glue to an
invertible $\cL$ on $X_T$ with $\cL|_{X_{T_i}}\cong\cL_i$.
1. ****(D2)**** *Effective closed immersions.* Closed
subschemes $Z_i\subseteq X_{T_i}$, finite flat of degree $d$ over
$T_i$, with cocycle-compatible cartesian identifications, glue to a
closed subscheme $Z\subseteq X_T$, finite flat of degree $d$ over
$T$, with $Z\times_TT_i\cong Z_i$.

## Proof

(D1): the fpqc sheaf sequence for $\cO$ and the functor
$\cM\mapsto\ker(\prod f_{i,*}\cM\rightrightarrows\cdots)$; flatness
and finite presentation are fpqc-local, hence so is finite local
freeness, which is equivalent to their conjunction. (D2): the ideals
$\cI_{Z_i}$ form a descent datum for quotient modules of $\cO_X$ by
(D1).
