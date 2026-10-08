+++
id = "sbc-lem-etale-locality"
kind = "lemma"
title = "Etale locality of the base-change map"
order = 1370
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-site", "sbc-def-base-change-map", "sbc-def-base-change-square"]
+++
Consider a base-change square
and let $\{U_i\to X\}$ be an etale covering such that $U_i\to S$ factors
as $U_i\to V_i\to S$ with $V_i\to S$ etale; form the associated
Cartesian diagrams

$$
\begin{array}{ccc}
U_i & \xleftarrow{h_i} & U_i\times_XY\\
f_i\big\downarrow & & \big\downarrow e_i\\
V_i & \xleftarrow{g_i} & V_i\times_ST,
\end{array}
$$

and put $\mathcal F_i=\mathcal F|_{V_i\times_ST}$ and
$K_i=K|_{V_i\times_ST}$ for a sheaf $\mathcal F$ resp. a complex $K$
on $T_{\Et}$.

1. If $f_i^{-1}g_{i,*}\mathcal F_i=h_{i,*}e_i^{-1}\mathcal F_i$ for
all $i$, then $f^{-1}g_*\mathcal F=h_*e^{-1}\mathcal F$.
1. If $f_i^{-1}Rg_{i,*}K_i=Rh_{i,*}e_i^{-1}K_i$ for all $i$, then
$f^{-1}Rg_*K=Rh_*e^{-1}K$.
1. If $\mathcal F$ is an abelian sheaf and
$f_i^{-1}R^qg_{i,*}\mathcal F_i=R^qh_{i,*}e_i^{-1}\mathcal F_i$
for all $i$, then
$f^{-1}R^qg_*\mathcal F=R^qh_*e^{-1}\mathcal F$.

(*Stacks Project, Lemma 59.86.1, [Tag `0EZR`](https://stacks.math.columbia.edu/tag/0EZR).*)

## Proof

Restricting to $U_i$ and using the factorizations
$U_i\to V_i\to S$ gives

$$
(f^{-1}g_*\mathcal F)|_{U_i}=f_i^{-1}(g_*\mathcal F|_{V_i})
=f_i^{-1}g_{i,*}\mathcal F_i,
$$

where the first equality is the compatibility of inverse and direct
images with localization of the etale site of
[def-weil-pbc-etale-site] (Sites, Lemma 7.28.2,
[Tag `03EF`](https://stacks.math.columbia.edu/tag/03EF)) and the second uses
$\mathcal F|_{V_i}=\mathcal F_i$, and likewise

$$
(h_*e^{-1}\mathcal F)|_{U_i}=h_{i,*}e_i^{-1}\mathcal F_i.
$$

Since $\{U_i\to X\}$ is an etale covering, a morphism of etale sheaves
whose restrictions to all $U_i$ are isomorphisms is an isomorphism
([def-weil-pbc-etale-site]), which proves (1); the assertions (2)
and (3) are the same argument with the localization compatibility for
the higher direct images and sheafified cohomology
(Cohomology on Sites, Lemma 21.20.4, [Tag `0D6G`](https://stacks.math.columbia.edu/tag/0D6G)), applied
degreewise for the $R^q$'s of [def-weil-pbc-direct-image] and to
$R^q$ of the base-change maps of [sbc-def-base-change-map].
