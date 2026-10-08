+++
id = "sk-rem-picard-seams"
kind = "section"
title = "The dependencies are one-way: $\\mathbf A\\Rightarrow\\mathbf B$ at four seams"
order = 870
+++
*Remark (sketch).*

The decomposition of Strand A and its spectral-sequence inputs into
makes the four seams visible.

1. ****$S_1$**** *Into the hypothesis check of the Hilbert
theorem* ([sk-thm-picard-hilb-curves]): the existence of an affine open
containing finitely many points of $X$ uses [sk-thm-picard-rr] (G)+(H)
(positive degree $\Rightarrow$ ample, ample effective divisor
$\Rightarrow$ affine complement), which are Riemann–Roch
consequences of [sk-thm-picard-duality] and [sk-thm-picard-pn].
1. ****$S_2$**** *Into the dictionary*
([sk-lem-picard-zero-dictionary]): $\deg Z(s)=\deg\cL_t=g$ is exactly
[sk-cor-picard-degree-g], i.e. [sk-thm-picard-rr] with
$\chi(\cL_t)=h^0=1$ and $\chi(\cO)=1-g$; this is what makes the
codomain $\underline{\Hilb}^g_{X/k}$ have index $g$, the same $g$ as
the genus—the equality of the two $g$'s is Riemann–Roch.
1. ****$S_3$**** *Into the openness of $F$*
([sk-lem-picard-f-open]): the openness of the locus where
$Rf_{T,*}\cL$ is finite locally free of rank $1$ in degree $0$ is
[sk-thm-picard-perfect] (perfect-locus openness, from the
semicontinuity [sk-thm-picard-semicon]), a
theorem about coherent families — the world of Strand A.
1. ****$S_4$**** *Into condition (2)(c)*
([sk-thm-picard-criterion]): the generation condition is precisely
[sk-thm-picard-twist] (Serre vanishing [sk-thm-picard-serre-b], Riemann–Roch
[sk-thm-picard-rr], density of rational points
[sk-prop-picard-dense-points]); without it the criterion has no input,
and without it $F$ would only give (2)(a), (2)(b).

Conversely, Strand B never feeds Strand A: no descent or
representability statement is used in the proofs of
[sk-thm-picard-cech]–[sk-thm-picard-twist]. This is why the correct
dependency picture is one chain, not two parallel ones.
