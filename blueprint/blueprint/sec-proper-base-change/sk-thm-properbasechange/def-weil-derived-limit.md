+++
id = "def-weil-derived-limit"
kind = "definition"
title = "Derived limit of an inverse system"
order = 1207
+++
Let $\mathcal D$ be a triangulated category and let $(K_n,f_n)_{n\in\mathbf
Z_{\geq1}}$ be an inverse system of objects of $\mathcal D$, with transition
maps $f_n:K_{n+1}\to K_n$. Assume that the countable product $\prod_nK_n$
exists in $\mathcal D$, and let

$$
 1-s:\prod_nK_n\longrightarrow\prod_nK_n,\qquad
 (k_n)_{n\in\mathbf Z_{\geq1}}\longmapsto
 \bigl(k_n-f_{n+1}(k_{n+1})\bigr)_{n\in\mathbf Z_{\geq1}}
$$

be the *transition endomorphism* of the system. An object $K\in\mathcal D$ is
a *derived limit*, or *homotopy limit*, of $(K_n,f_n)$ if it is the first
term of a distinguished triangle

$$
 K\longrightarrow\prod_nK_n\xrightarrow{\ 1-s\ }\prod_nK_n
 \longrightarrow K[1],
$$

and one then writes $K=R\varprojlim_nK_n$. The displayed triangle is the
*Roos triangle* of the system. The definition is made inside the triangulated
category $\mathcal D$, for an inverse system of objects *of* $\mathcal D$: no
resolution of the system is chosen and no model for $\mathcal D$ is fixed. It
is Definition 13.34.1 of the Stacks Project, Tag
[08TC](https://stacks.math.columbia.edu/tag/08TC).
