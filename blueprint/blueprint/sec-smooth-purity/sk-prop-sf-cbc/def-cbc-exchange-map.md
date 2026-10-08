+++
id = "def-cbc-exchange-map"
kind = "definition"
title = "Compact-support exchange map"
order = 1528
uses = ["cor-cbc-derived-extension-zero-base-change", "def-cbc-compact-support-square", "def-compact-support-direct-image-detailed", "def-exchange-projection", "def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange"]
+++
Let $\square$ be a
compact-support
base-change square with $f:X\to Y$ separated of finite type, let
$\Lambda$ be a finite commutative ring, and let $K\in D^+(X_{\Et},\Lambda)$.
Choose a compactification $c=(j,p)$ of $f$ and its base change
$c'$; the
compact-support direct
image satisfies

$$
Rf_!K=Rp_*j_!K,\qquad Rf'_!K=Rp'_*j'_!K.
$$

The *compact-support exchange map* is

$$
\operatorname{Ex}_!(K):g^{-1}Rf_!K\longrightarrow Rf'_!g'^{-1}K,
$$

the composite of the
derived exchange morphism
of [def-weil-pbc-cartesian-square] for the proper $p$ and the
cartesian square $(\bar g',p')$, applied to $j_!K$, with the
extension-by-zero identification
$g^{-1}j_!K\xrightarrow{\sim}j'_!g_U^{-1}K=j'_!g'^{-1}K$ of
[cor-cbc-derived-extension-zero-base-change]; this is the map
denoted $\operatorname{Ex}_!$ in [def-exchange-projection].
