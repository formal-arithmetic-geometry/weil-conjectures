+++
id = "def-pur-vector-bundle-thom-class"
kind = "definition"
title = "Thom class of a vector bundle"
order = 1988
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-vector-bundle-zero-section", "def-weil-derived-tensor", "thm-pur-localized-top-chern", "thm-pur-projective-bundle-formula"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $E\to B$ be a
vector bundle of constant
rank $r$, with zero section $z$ and projection $\pi$. The
tautological section of $\pi^*E$ has zero scheme $z(B)$; its
localized top Chern class of [thm-pur-localized-top-chern] is the
supported class

$$
\operatorname{thom}(E):z_*\Lambda_B\longrightarrow\Lambda_E(r)[2r].
$$

Applying $R\pi_!$ defines

$$
\tau_E:\Lambda_B\longrightarrow R\pi_!\Lambda_E(r)[2r].
$$

Explicitly, with $\overline E=\mathbf P_B(E\oplus\mathcal O_B)$ and
the localization triangle of the open $E=\overline E\setminus \mathbf P_B(E)$ of def:weil-open-closed-recollement, the two
[thm-pur-projective-bundle-formula] decompositions for the
$\mathbf P^r$-bundle $\overline E\to B$ and the $\mathbf P^{r-1}$-bundle $\mathbf P_B(E)\to B$ identify the fiber of the
restriction map with

$$
R\pi_!\Lambda_E\;\cong\;\Lambda_B(-r)[-2r].
$$

Under a local decomposition $E\simeq L_1\oplus\cdots\oplus L_r$ the
supported class is $\operatorname{thom}(L_1)\smile\cdots\smile \operatorname{thom}(L_r)$.
