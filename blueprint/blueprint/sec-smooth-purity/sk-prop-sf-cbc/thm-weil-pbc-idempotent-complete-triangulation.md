+++
id = "thm-weil-pbc-idempotent-complete-triangulation"
kind = "theorem"
title = "Idempotent-complete triangulation"
order = 1544
uses = ["def-weil-karoubi-envelope", "def-weil-pbc-finite-stage-pair-category", "def-weil-pbc-qbar-category", "lem-weil-karoubi-envelope-triangulated", "prop-weil-pbc-common-stage-calculus", "thm-weil-pbc-qbar-idempotent-complete", "thm-weil-pbc-verdier-axioms"]
+++
The scalar operation of [def-weil-pbc-qbar-category] is independent of $N$
and of the representative of $f$ and makes $\mathcal P_T=\Dbc(T,\Qlb)$
$\Qlb$-linear. The shift and distinguished triangles of
[def-weil-pbc-qbar-category] give $\Dbc(T,\Qlb)$ the structure of an
idempotent-complete ordinary triangulated category, and the canonical
functor $\Dbc(T,\Qlb)\to\Kar(\Dbc(T,\Qlb))$ is an exact equivalence. For
every finite $E$ the composite
$$
 \Dbc(T,E)\xrightarrow{j_E}\mathcal P_T=\Dbc(T,\Qlb)
$$
is exact and $E$-linear.

*Source note:* no Stacks Project entry states this form: the ledger's
verified entries contain no statement making a filtered colimit of
triangulated categories triangulated, and the blueprint adds the
$\Qlb$-linearity, the idempotent-complete triangulation and the exactness of
the finite-stage inclusions $j_E$. What Stacks does provide, each page
fetched and quoted, is the definition of the structure asserted here —
Definition 13.3.2 ([Tag 0145](https://stacks.math.columbia.edu/tag/0145),
TR1--TR4 with the octahedral axiom) with Definition 13.3.3 ([Tag
014V](https://stacks.math.columbia.edu/tag/014V), exact functor) — the
verification of the axioms for a localization, Proposition 13.5.6 ([Tag
05R6](https://stacks.math.columbia.edu/tag/05R6)), and the Karoubianity
criterion Lemma 13.4.14 ([Tag
05QW](https://stacks.math.columbia.edu/tag/05QW)). Difference: all of these
live in one additive category over one fixed coefficient ring, whereas the
statement here concerns the filtered colimit $\mathcal P_T$ with its
$\Qlb$-scalar action.

## Proof

The scalar operation of [def-weil-pbc-qbar-category] is independent of $N$:
for two finite fields $N,N'$ containing $\Ql(\alpha)$ and the stage $M$, the
representatives $\alpha u_N$ and $\alpha u_{N'}$ transport to their
compositum and agree there, since $T_{P/N}$ and $T_{P/N'}$ are linear over
$N$ and $N'$ (hence over $N\cap N'$ containing $\Ql(\alpha)$); independence
of the representative of $f$ holds through the representative equivalence
relation of [def-weil-pbc-finite-stage-pair-category]: transport an equality
$u_P=v_P$, which survives scalar multiplication. The field laws and
bilinearity hold at a common stage by
[prop-weil-pbc-common-stage-calculus], so $\mathcal P_T$ is $\Qlb$-linear.
By [thm-weil-pbc-verdier-axioms], $\mathcal P_T=\Dbc(T,\Qlb)$ is
triangulated, and it is idempotent complete by
[thm-weil-pbc-qbar-idempotent-complete], so the canonical fully faithful
functor into the Karoubi envelope is an equivalence by that theorem, hence
exact. The composite $j_E$ is exact by [thm-weil-pbc-verdier-axioms], and
$E$-linear and $\Qlb$-linear by the displayed scalar definition.
