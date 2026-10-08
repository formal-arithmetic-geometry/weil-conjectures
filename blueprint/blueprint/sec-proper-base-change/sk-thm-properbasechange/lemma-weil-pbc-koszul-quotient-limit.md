+++
id = "lemma-weil-pbc-koszul-quotient-limit"
kind = "lemma"
title = "Koszul and quotient towers have the same limit"
order = 1259
uses = ["def-weil-pbc-adic-derived-inverse-limit", "def-weil-pbc-complete-coefficient-datum", "def-weil-pbc-completion-map", "def-weil-pbc-intrinsic-koszul-completion"]
+++
There is a functorial isomorphism

$$
c_K:K^{\wedge,\mathrm{Kos}}\xrightarrow{\sim}
R\varprojlim_nK_n
$$

such that $c_K\kappa_K=\operatorname{comp}_K$.

## Proof

Put $J_m=(f_1^m,\ldots,f_r^m)$. The augmentation
$Q_m\to\Lambda/J_m$ has cone $\tau_{<0}Q_m$. For $p<0$ the modules
$H^p(Q_m)$ are finite and killed by $J_m$. The transition in degree $p$
has entries in $(f_1^{b-a},\ldots,f_r^{b-a})$ from level $b$ to level $a$.
Artin–Rees, applied to the cycles inside the finite free term $Q_a^p$,
therefore makes $H^p(Q_b)\to H^p(Q_a)$ zero for $b\gg a$. Hence
$(\tau_{<0}Q_m)_m$ is pro-zero and
$(Q_m)_m\to(\Lambda/J_m)_m$ is a pro-isomorphism.

The inclusions

$$
I^{r(m-1)+1}\subseteq J_m\subseteq I^m
$$

show that $(\Lambda/J_m)_m$ and $(P_n)_n$ are cofinal pro-systems. Tensor
the comparison maps with $K$ and apply the product-cone limit. Pro-zero
cones have zero product-cone limit after a cofinal reindexing, so the result
is $c_K$. Both units are induced by the same augmentations
$\Lambda\to Q_m\to\Lambda/J_m\to P_n$; this proves the triangle equation.
