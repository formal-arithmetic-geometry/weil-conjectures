+++
id = "lemma-nagata-glue-finite-type-ideals"
kind = "lemma"
title = "Gluing compatible finite-type ideals on two qc opens"
order = 165
+++
**Status.** Bypassed by the formalized route: a finite-type ideal is
extended from a quasi-compact open in one step by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_comap_eq`,
so no separate two-open gluing lemma is needed.

Let $U,W\subseteq X$ be quasi-compact opens of a qcqs scheme. If
$\mathcal I_U\subseteq\mathcal O_U$ and
$\mathcal I_W\subseteq\mathcal O_W$ are finite type quasi-coherent ideals
equipped with an equality of their restrictions to $U\cap W$, then there is
a finite type quasi-coherent ideal
$\mathcal I_{U\cup W}\subseteq\mathcal O_{U\cup W}$ restricting to the two
given ideals.

## Proof

The specified equality is an isomorphism of ideal sheaves compatible with
the inclusions into the structure sheaf. The sheaf gluing theorem for the
open cover $U\cup W=U\cup W$ therefore glues the ideals and inclusions to a
subsheaf of $\mathcal O_{U\cup W}$. Quasi-coherence, the ideal property,
and finite type are local on this cover, so they hold for the glued ideal.
