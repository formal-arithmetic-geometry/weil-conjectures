+++
id = "cor-weil-boundary-duality-discharge"
kind = "theorem"
title = "The finite-stage boundary input is a consequence"
order = 2137
tags = ["latex:corollary"]
uses = ["def-weil-boundary-duality-input", "lem-weil-closed-costalk-duality", "lem-weil-duality-pairing", "thm-fix-general-biduality"]
+++
The boundary duality input of [def-weil-boundary-duality-input]
holds for every separated finite-type $Y/k$ and every finite stage
$A=A_{E,n}$. In particular the canonical evaluation-defined map

$$
\beta_L:i^*D_TL\longrightarrow D_ZRi^!L
$$

is an isomorphism for every closed immersion $i:Z\hookrightarrow T$
between the locally closed pieces in that definition.

## Proof

Preservation in the first clause of
[def-weil-boundary-duality-input] is part of
[thm-fix-general-biduality], applied to every piece.
The independently formal comparison
$\alpha_{D_TL}:Ri^!D_TD_TL\cong D_Zi^*D_TL$ of
[lem-weil-closed-costalk-duality], composed with $Ri^!\delta_L$,
identifies $Ri^!L$ with $D_Zi^*D_TL$.
In particular $Ri^!L$ is finite-Tor constructible. Apply $D_Z$
and use biduality on $Z$:

$$
D_ZRi^!L\cong D_ZD_Zi^*D_TL\cong i^*D_TL.
$$

The inverse of this composite is $\beta_L$. Indeed, adjointing
back through tensor–Hom and $i_*\dashv Ri^!$, both maps correspond
to the restriction of the evaluation
$D_TL\otimes^L L\to\omega_T$. The evaluation identities in
[lem-weil-duality-pairing] then also give exactly the compatibility
between $\beta_{D_TK}$, $\alpha_K$, and $i^*\delta_K$ required
in the second clause of the definition. Thus boundary exchange is
derived after biduality and was not used to prove it.
