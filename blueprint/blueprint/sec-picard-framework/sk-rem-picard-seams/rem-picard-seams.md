+++
id = "rem-picard-seams"
kind = "remark"
title = "The dependencies are one-way: $\\mathbf A\\Rightarrow\\mathbf B$ at four seams"
order = 871
+++
The decomposition of Strand A and its spectral-sequence inputs into
makes the four seams visible.

1. ****$S_1$**** *Into the hypothesis check of the Hilbert
theorem* ([thm-pc-hilb-curves]): the existence of an affine open
containing finitely many points of $X$ uses the Riemann–Roch consequences
[lem-sc-positive-degree-ample] (positive degree $\Rightarrow$ ample) and
[lem-sc-ample-complement-affine] (ample effective divisor
$\Rightarrow$ affine complement), which are Riemann–Roch
consequences of [thm-sc-serre-duality-curve] and [lem-pc-projective-space-twist-cohomology].
1. ****$S_2$**** *Into the dictionary*
([lem-pc-zero-scheme-recd]): $\deg Z(s)=\deg\cL_t=g$ is exactly
[cor-picard-degree-g], i.e. [lem-sc-riemann-roch] with
$\chi(\cL_t)=h^0=1$ and $\chi(\cO)=1-g$; this is what makes the
codomain $\underline{\Hilb}^g_{X/k}$ have index $g$, the same $g$ as
the genus—the equality of the two $g$'s is Riemann–Roch.
1. ****$S_3$**** *Into the openness of $F$*
([lem-pc-f-open-subfunctor]): the openness of the locus where
$Rf_{T,*}\cL$ is finite locally free of rank $1$ in degree $0$ is
[lem-pc-perfect-locus] (perfect-locus openness, from the
semicontinuity [lem-pc-rf-perfect-base-change]), a
theorem about coherent families — the world of Strand A.
1. ****$S_4$**** *Into condition (2)(c)*
([thm-pc-criterion]): the generation condition is precisely
[lem-pc-twist] (Serre vanishing [lem-pc-serre-vanishing], Riemann–Roch
[lem-sc-riemann-roch], density of rational points
[lem-pc-rational-points-dense]); without it the criterion has no input,
and without it $F$ would only give (2)(a), (2)(b).

Conversely, Strand B never feeds Strand A: no descent or
representability statement is used in the proofs of
[lem-sc-cech-spectral]–[lem-pc-twist]. This is why the correct
dependency picture is one chain, not two parallel ones.
