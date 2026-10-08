+++
id = "lem-sc-riemann-roch-large-degree"
kind = "lemma"
title = "Sections of line bundles of degree at least $2g-1$"
order = 717
uses = ["def-sc-curves", "def-sc-genus", "def-sc-pic0", "lem-sc-canonical-degree", "lem-sc-negative-degree-no-sections", "lem-sc-riemann-roch", "thm-sc-serre-duality-curve"]
+++
Let $k$ be algebraically closed, $C$ a proper smooth connected curve of
genus $g$ ([def-sc-genus]) over $k$, and $\mathcal L$ a line bundle on
$C$ of degree $d=\deg\mathcal L\ge2g-1$ ([def-sc-pic0]). Then
$H^1(C,\mathcal L)=0$ and

$$
h^0(\mathcal L):=\dim_kH^0(C,\mathcal L)=d+1-g.
$$

## Proof

By Serre duality ([thm-sc-serre-duality-curve]),

$$
H^1(C,\mathcal L)^{\vee}\cong H^0\bigl(C,\Omega^1_{C/k}\otimes\mathcal L^{-1}\bigr).
$$

Here $\Omega^1_{C/k}=\omega_C=\mathcal O_C(K_C)$ with
$\deg K_C=2g-2$ ([lem-sc-canonical-degree]), so, $\deg$ being a
homomorphism on $\operatorname{Pic}(C)$ ([def-sc-pic0]),

$$
\deg\bigl(\Omega^1_{C/k}\otimes\mathcal L^{-1}\bigr)=(2g-2)-d\le-1<0 .
$$

A line bundle of negative degree has no nonzero global sections
([lem-sc-negative-degree-no-sections]), so the right-hand side vanishes
and $H^1(C,\mathcal L)=0$. Since also $H^q(C,\mathcal L)=0$ for
$q\ge2$, Riemann–Roch ([lem-sc-riemann-roch], part (1)) gives

$$
\dim_kH^0(C,\mathcal L)=\chi(C,\mathcal L)=d+1-g.
$$
