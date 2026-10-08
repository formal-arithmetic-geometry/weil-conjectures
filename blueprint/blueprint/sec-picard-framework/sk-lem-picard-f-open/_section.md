+++
id = "sk-lem-picard-f-open"
kind = "section"
title = "$F$ is an open subfunctor"
order = 821
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι"]
+++
*Lemma (sketch).*

$F\subseteq G$ is a subfunctor and the inclusion is representable by
open immersions.

## Proof

*(This is the seam $S_3$.)* Apply [sk-thm-picard-perfect] to the
proper morphism $f_T:X_T\to T$ of finite presentation and the flat
family $\cL$ of finite presentation: for $i=0$, $r=1$ the locus
where $Rf_{T,*}\cL$ is finite locally free of rank $1$ in degree
$0$ is open, and the same computation with a shifted degree covers
the general case. Subfunctor property: base change of the statement
([sk-thm-picard-semicon] and the base-change comparison).
