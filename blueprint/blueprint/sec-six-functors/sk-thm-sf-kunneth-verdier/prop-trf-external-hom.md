+++
id = "prop-trf-external-hom"
kind = "theorem"
title = "External Hom; the $\\beta$ map"
order = 2227
tags = ["latex:proposition"]
uses = ["def-sf-kv-maps", "def-trf-admissibility", "lem-sf-tensor-hom", "lem-trf-devissage-generation", "lem-trf-ordinary-kunneth", "prop-sf-dualizable-hom", "prop-trf-exceptional-kunneth"]
+++
For $i=1,2$, let $E_i\in D^b_{ctf}(X_i,A)$ and $L_i\in D^b_{ctf}(X_i,A)$ on separated finite-type $X_i$, with the
admissibility of [def-trf-admissibility] where $!$-pullbacks
occur. The evaluation-defined comparison of [def-sf-kv-maps] (iii)

$$
\beta:\RHom_A(E_1,L_1)\boxtimes_A^{\mathrm L}\RHom_A(E_2,L_2)
\longrightarrow
\RHom_A\bigl(E_1\boxtimes_A^{\mathrm L}E_2,\,
L_1\boxtimes_A^{\mathrm L}L_2\bigr)
$$

is an isomorphism, natural in all four variables.

## Proof

Both sides are exact in each $E_i$, so devissage in both $E_i$ by the
generation [lem-trf-devissage-generation] (generators $Rg_*j_!F$ with $F$ lisse with flat stalks on a
stratum) reduces to $E_i=Rh_{i!}F_i$, where $h_i=g_ij_i$ with $g_i$ finite
and $j_i$ open, and $F_i$ is lisse on $U_i$ with flat stalks. The stalks of
$F_i$ are finite flat, hence free, over the local ring $A$, so $F_i$ is
locally finite free, hence perfect, and [prop-sf-dualizable-hom] gives
$\RHom_A(F_i,-)\simeq F_i^\vee\otimes^{\mathrm L}_A-$. The tensor–Hom
and exceptional adjunctions ([lem-sf-tensor-hom]) give

$$
\RHom_A(E_i,L_i)\simeq Rh_{i*}\RHom_A(F_i,h_i^!L_i)
\simeq Rh_{i*}\bigl(F_i^\vee\otimes^{\mathrm L}_Ah_i^!L_i\bigr).
$$

Writing $h=h_1\times h_2$ and $F=F_1\boxtimes_A^{\mathrm L}F_2$, so that
$F^\vee\simeq F_1^\vee\boxtimes_A^{\mathrm L}F_2^\vee$ and
$E_1\boxtimes_A^{\mathrm L}E_2\simeq Rh_!F$ by the $!$-Kunneth map, the
comparison becomes

$$
Rh_{1*}\bigl(F_1^\vee\otimes h_1^!L_1\bigr)\boxtimes_A^{\mathrm L}
Rh_{2*}\bigl(F_2^\vee\otimes h_2^!L_2\bigr)
\xrightarrow[\text{twice}]{\mathrm{Ku}_*}
Rh_*\bigl(F^\vee\otimes(h_1^!L_1\boxtimes_A^{\mathrm L}h_2^!L_2)\bigr)
\xrightarrow{Rh_*(1\otimes\alpha)}
Rh_*\bigl(F^\vee\otimes h^!(L_1\boxtimes_A^{\mathrm L}L_2)\bigr),
$$

whose target is $\RHom_A(E_1\boxtimes_A^{\mathrm L}E_2,L_1\boxtimes_A^{\mathrm L}L_2)$
by the same identifications;
the first arrow being [lem-trf-ordinary-kunneth] applied in each
factor (after the symmetry of the tensor product), and the second the exceptional Kunneth
[prop-trf-exceptional-kunneth]. To identify this composite with the
specified $\beta$, take ordinary and then exceptional adjoints: both
paths become the tensor product of the two evaluation maps after the
projection formula. Hence $\beta$ itself is an isomorphism.
