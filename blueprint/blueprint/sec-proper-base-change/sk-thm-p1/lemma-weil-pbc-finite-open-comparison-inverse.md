+++
id = "lemma-weil-pbc-finite-open-comparison-inverse"
kind = "lemma"
title = "Section and stalk inverse for the finite-open map"
order = 1175
uses = ["def-weil-pbc-finite-open-comparison"]
+++
The map $\beta_{\bar v,j_Y,G}$ is an isomorphism. Its inverse is obtained by
restricting to $U$, collecting the finite-fibre tuple on $V$, and extending
that tuple by zero to $Y$; both inverse equations hold on sections and on
geometric stalks.

## Proof

Let $T\to Y$ be etale and put
$T_V=T\times_YV$, $T_X=T\times_YX$, and
$T_U=T\times_YU$. A section of $(j_Y)_!v_*G$ over $T$ is etale-locally a
finite tuple

$$
(s_x)_{x\in T_U/T_V},\qquad s_x\in G
$$

on $T_V$, extended by zero on $T\setminus T_V$. The section map
$\beta(T)$ sends this tuple to the identical tuple on $T_U\subset T_X$ and
extends it by zero on $T_X\setminus T_U$. This is a section of
$(j_X)_!G$ because the support remains closed after the finite map
$T_X\to T$. Restriction along a map $T'\to T$ pulls back every component,
so these section maps define a sheaf morphism and agree with the
adjunction definition.

Conversely, take
$a\in\Gamma(T_X,(j_X)_!G)$. Restrict $a$ to $T_U$ and group its components
over the finite fibres of $T_U\to T_V$. Since $a$ vanishes at every
geometric point of $T_X\setminus T_U$, the grouped tuple vanishes at every
geometric point of $T\setminus T_V$ and therefore defines a section
$\gamma(T)(a)\in\Gamma(T,(j_Y)_!v_*G)$. Restriction preserves the grouping,
so the $\gamma(T)$ define a sheaf morphism

$$
\gamma_{\bar v,j_Y,G}:\bar v_*(j_X)_!G\longrightarrow(j_Y)_!v_*G.
$$

At a geometric point $\bar y\to Y$, the two stalks are

$$
\begin{cases}
\displaystyle\bigoplus_{\bar x\mapsto\bar y}G_{\bar x},
&\bar y\in V,\\[6pt]
0,&\bar y\notin V.
\end{cases}
$$

Here a point $\bar x$ above $\bar y\in V$ lies in $U$ by Cartesianity.
Both $\beta_{\bar y}$ and $\gamma_{\bar y}$ are the identity of the displayed
finite sum; outside $V$ both are the zero map of the zero group. Hence

$$
\gamma_{\bar v,j_Y,G}\circ\beta_{\bar v,j_Y,G}
=\operatorname{id}_{(j_Y)_!v_*G},\qquad
\beta_{\bar v,j_Y,G}\circ\gamma_{\bar v,j_Y,G}
=\operatorname{id}_{\bar v_*(j_X)_!G}
$$

on all geometric stalks. Conservativity of geometric stalks proves both
equations as sheaf maps.
