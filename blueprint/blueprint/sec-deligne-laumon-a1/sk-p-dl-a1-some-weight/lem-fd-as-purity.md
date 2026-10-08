+++
id = "lem-fd-as-purity"
kind = "lemma"
title = "Purity of the Artin–Schreier sheaf"
order = 2771
uses = ["def-fd-artin-schreier-sheaf", "def-weil-punctual-weights", "lem-fd-as-lisse", "lem-fd-as-trace", "lem-tw-root-of-unity-modulus"]
+++
Let $k_0=\mathbf F_q$ and fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$ as in
[def-weil-punctual-weights]. The Artin–Schreier sheaf
$\mathcal L_{\psi,ax}$ on $\mathbf A^1_{k_0}$ is punctually
$\iota$-pure of weight $0$.

## Proof

By [lem-fd-as-lisse] the sheaf is lisse of rank one, so at every
closed point $u$ its unique local Frobenius eigenvalue is the trace
value $t_{\mathcal L_{\psi,ax}}(u)$ of [lem-fd-as-trace], namely
$\psi(\operatorname{Tr}_{\kappa(u)/k_0}(au))$: a root of unity,
of modulus one by [lem-tw-root-of-unity-modulus]. Hence every
local eigenvalue satisfies $|\iota(\alpha)|=1=q_u^{0/2}$, which is the
punctual $\iota$-purity of weight $0$ of
[def-weil-punctual-weights].
