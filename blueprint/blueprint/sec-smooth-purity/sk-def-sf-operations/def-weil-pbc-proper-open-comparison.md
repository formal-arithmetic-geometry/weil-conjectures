+++
id = "def-weil-pbc-proper-open-comparison"
kind = "definition"
title = "Comparison map for a proper map fixing an open"
order = 1475
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions"]
+++
Let $u:T_1\to T_2$ be
proper, and let
$j_i:X\hookrightarrow T_i$ be
open immersions with
$u j_1=j_2$. Fix a finite ring $\Lambda$ and
$K\in\hyperref[def-weil-pbc-derived-categories]{D^+(X_{\Et},\Lambda)}$.
Set $V=T_1\times_{T_2}X$, with projections $b:V\to T_1$ and
$p:V\to X$, and let $s:X\to V$ be the morphism induced by $j_1$,
so that $b s=j_1$ and $p s=\operatorname{id}_X$. Define

$$
\alpha_{u,K}:j_{2!}K\longrightarrow Ru_*j_{1!}K
$$

to be the adjoint, under $j_{2!}\dashv j_2^{-1}$, of
$\theta_{u,K}^{-1}$. The functor $Ru_*$ here is the
derived direct image.
