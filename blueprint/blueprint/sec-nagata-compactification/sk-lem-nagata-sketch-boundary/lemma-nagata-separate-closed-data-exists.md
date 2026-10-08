+++
id = "lemma-nagata-separate-closed-data-exists"
kind = "lemma"
title = "Preparation data for separating two closed boundaries, [stacks-project]"
order = 246
uses = ["def-nagata-admissible-blowup", "def-nagata-qc-open-complement-ideal", "def-nagata-strict-transform", "lemma-nagata-chart-generator-regular", "lemma-nagata-finite-type-nil-ideal-nilpotent"]
+++
**Status.** Bypassed by the formalized route: boundary separation is
`AlgebraicGeometry.separationBlowup` with
`AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`,
proved from Deligne's disjointness blow-up rather than from this
preparation.

Let $X$ be qcqs, let $U\subseteq X$ be quasi-compact open, and let
$Z_i=V(\mathcal I_i)\hookrightarrow X$ be finite-presentation closed
immersions with $Z_1\cap Z_2\cap U=\varnothing$. Put
$Z=V(\mathcal I_1\mathcal I_2)$, $U_Z=Z\times_XU$, and
$P_i=Z_i\times_XU$. The two closed subschemes $P_i$ are the disjoint
open-and-closed components of $U_Z=P_1\amalg P_2$. There is a finite
presentation closed center $C\hookrightarrow Z$, disjoint from $U_Z$, such
that the blow-up $Z' = \operatorname{Bl}_C(Z)\to Z$ is $U_Z$-admissible
and the strict transforms of $Z_1$ and $Z_2$ in $Z'$ are disjoint.

## Proof

Put $K_i=\mathcal I_Z(P_i)$, the finite-type ideal whose vanishing set is
$Z\setminus P_i$ ([def-nagata-qc-open-complement-ideal]). Since
$P_1$ and $P_2$ are disjoint, $V(K_1K_2)=Z$; finite type and
quasi-compactness therefore give $N>0$ with $(K_1K_2)^N=0$ by
[lemma-nagata-finite-type-nil-ideal-nilpotent]. The restrictions of
both $K_i$ to the quasi-compact closed boundary $Z\setminus U_Z$ are finite
type nil ideals, so enlarge $N$ until those restrictions are also killed by
the $N$th power. Replace $K_i$ by $K_i^N$; their vanishing sets are
unchanged, now $K_1K_2=0$, and both ideals vanish on $Z\setminus U_Z$. Let
$J=K_1+K_2$ and $C=V(J)$. On $U_Z=P_1\amalg P_2$, $K_1$ is the unit ideal
on $P_1$ and zero on $P_2$, while $K_2$ has the opposite behaviour. Hence
$J|_{U_Z}=\mathcal O_{U_Z}$ and $J$ vanishes on $Z\setminus U_Z$. Thus
$Z\setminus C=U_Z$ and $C\cap U_Z=\varnothing$. The closed
immersion $C\hookrightarrow Z$ is finite presentation because $J$ is finite
type.

Work on an affine open $\operatorname{Spec}(A)\subseteq Z$, with generators
$(a_\alpha)$ of $K_1$ and $(b_\beta)$ of $K_2$. The blow-up of $J$ is
covered by $A[J/a_\alpha]$ and $A[J/b_\beta]$. In
$A[J/a_\alpha]$, the element $a_\alpha$ is a nonzerodivisor by
[lemma-nagata-chart-generator-regular]; since
$a_\alpha K_2=0$, it follows that $K_2A[J/a_\alpha]=0$. Interchanging
the roles of $K_1$ and $K_2$ gives $K_1A[J/b_\beta]=0$. An
$a_\alpha$-chart and a $b_\beta$-chart have empty
intersection: on their overlap $a_\alpha b_\beta$ is both zero and a
nonzerodivisor, so the overlap ring is zero. Consequently the blow-up is a
disjoint union of the open-and-closed union $Z'_1$ of the $a_\alpha$-charts
and the open-and-closed union $Z'_2$ of the $b_\beta$-charts; the construction
is intrinsic in the extended ideals $K_i\mathcal O_{Z'}$, so these local
decompositions glue.

Over $U_Z$, the inverse image of $P_i$ lies in $Z'_i$. The strict transform
of $Z_i\to Z$ is the scheme-theoretic closure of that inverse image. Since
$Z'_i$ is closed as well as open, this closure remains in $Z'_i$. The two
strict transforms are therefore disjoint.
