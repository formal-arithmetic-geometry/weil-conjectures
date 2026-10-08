+++
id = "prop-pc-xk-integral"
kind = "theorem"
title = "Base changes of $X$ are smooth projective curves"
order = 760
tags = ["latex:proposition"]
uses = ["def-pc-curve", "def-pc-rational-point", "def-pc-separably-closed", "def-pc-smooth-projective-curve", "lem-pc-closed-imm-base-change", "lem-pc-dim-base-change", "lem-pc-flat-base-change-cohom", "lem-pc-flat-field", "lem-pc-h0-geom-connected", "lem-pc-h0-proper-variety", "lem-pc-projective-proper", "lem-pc-proper-base-change", "lem-sc-smooth-regular", "rem-pc-regular-normal"]
+++
Let $k$ be a separably closed field
and let $X$ be a smooth
projective curve over $k$ with a
$k$-rational point $\sigma$. Then:

1. $H^0(X,\mathcal{O}_X)=k$ and $f_*\mathcal{O}_X=\mathcal{O}_k$ (where $f:X\to\operatorname{Spec} k$);
1. for every field extension $K/k$, the
base change $X_K$ is a smooth
projective curve over $K$ (in particular $X_K$ is integral, and $X$ is
geometrically integral), with $H^0(X_K,\mathcal{O}_{X_K})=K$ and
$\dim_KH^1(X_K,\mathcal{O}_{X_K})=\dim_kH^1(X,\mathcal{O}_X)$.

## Proof

Since $X$ is a proper variety (projective $\Rightarrow$ proper,
[lem-pc-projective-proper]; a curve is a variety, hence integral,
[def-pc-curve]), the ring $k':=H^0(X,\mathcal{O}_X)$ is a finite field
extension of $k$ by [lem-pc-h0-proper-variety] (1). The section
$\sigma$ gives a $k$-algebra homomorphism $\sigma^\#:H^0(X,\mathcal{O}_X)\to H^0(\operatorname{Spec}(k),\mathcal{O}_k)=k$, and a field homomorphism $k'\to k$ over $k$ is
injective; hence $[k':k]=1$, i.e. $k'=k$; since $H^0(X,\mathcal{O}_X)=k$ the
quasi-coherent $\mathcal{O}_k$-module $f_*\mathcal{O}_X$ is free of rank one, so
$f_*\mathcal{O}_X=\mathcal{O}_k$. This proves (1).

For (2): let $K/k$ be a field extension and let
$g:\operatorname{Spec}(K)\to\operatorname{Spec}(k)$. The base change $g$ is flat
([lem-pc-flat-field]), and $f$ is quasi-compact and quasi-separated
(proper, [lem-pc-projective-proper]), so by
[lem-pc-flat-base-change-cohom] applied to $\mathcal{F}=\mathcal{O}_X$,

$$
g^*f_*\mathcal{O}_X\;\cong\;f_{K,*}\mathcal{O}_{X_K},
$$

hence $f_{K,*}\mathcal{O}_{X_K}=\mathcal{O}_K$ and $H^0(X_K,\mathcal{O}_{X_K})=K$; likewise
$H^1(X_K,\mathcal{O}_{X_K})\cong H^1(X,\mathcal{O}_X)\otimes_kK$, whence
$\dim_K H^1(X_K,\mathcal{O}_{X_K})=\dim_kH^1(X,\mathcal{O}_X)$.
The morphism $X_K\to\operatorname{Spec}(K)$ is smooth (base change of smooth,
[lem-pc-proper-base-change]) and proper (base change of proper,
[lem-pc-proper-base-change]), so $X_K$ is regular
([lem-sc-smooth-regular]), hence normal ([rem-pc-regular-normal])
and reduced. Moreover $X_K$ is geometrically reduced: for every $K'/K$,
$X_{K'}$ is smooth over $K'$, hence regular, hence reduced; and $X_K$ is
proper, so [lem-pc-h0-geom-connected] (with $k$ replaced by $K$ and
$X$ by $X_K$) shows that $X_K$ is geometrically connected, in particular
connected. A Noetherian normal connected scheme is irreducible by
[rem-pc-regular-normal]: the normal scheme $X_K$ is a finite disjoint
union of normal integral schemes, and connectedness forces a single
component. Hence $X_K$ is integral. By [lem-pc-dim-base-change]
the dimension of $X_K$ is $1$, and $X_K\to\operatorname{Spec}(K)$ is of finite type and
separated (base changes of finite type and separated morphisms), so $X_K$
is a variety of dimension $1$, i.e. a curve ([def-pc-curve]).
Finally $X_K$ is projective: the closed immersion
$i:X\to\mathbf{P}^n_k$ base changes to a closed immersion
$i_K:X_K\to\mathbf{P}^n_K$ ([lem-pc-closed-imm-base-change]). This proves
(2); applying (2) to $K=k$ (and all extensions) gives geometric
integrality of $X$.
